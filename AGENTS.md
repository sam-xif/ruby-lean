# AGENTS.md

Instructions for coding agents working in this repository. Human contributors:
see [`docs/contributing.md`](docs/contributing.md), which says the same at
greater length.

## Before you commit

```sh
make check
```

It must end with `make check: ALL CHECKS PASSED`. It lints, builds the model,
builds every proof book (the type checker is part of one), audits axioms, runs
the checker over its corpus, runs the unit tests, and runs the model against
CRuby. Do not commit on a failure, do not skip a failing target, and do not
weaken a check to make it pass.

Then, before opening a pull request:

```sh
make check-not-weakened
```

It compares your change with `origin/main` and fails if a recorded result fell,
a check or an audited theorem was dropped, a `sorry`, `native_decide`, axiom,
lint suppression or test skip was added, or the number of tests fell. CI runs
the same comparison, from `main`'s copy of the script, on every pull request.

While iterating, run the narrower target for what you changed (`make help`
lists them), then `make check` once at the end:

| Changed | Run |
|---|---|
| `ruby-lean/RubyCore/`, `ruby-lean/prelude/` | `make conformance`, then `make books` |
| `books/Books/TypeSoundness/Checker/` | `make soundness` |
| anything else under `books/` | `make books` |
| `desugar/` | `make desugar-unit desugar-test desugar-coverage` |
| `books/scripts/emit_deriv.rb`, `books/scripts/read_sigs.rb` | `make emitter-unit` |
| `difftest/` | `make difftest-test` |
| `docs/`, any README | `make docs` |
| any Python, Ruby tooling, shell script or workflow | `make lint` (`make format` fixes what it can) |

The proofs are a separate Lake package (`books/`). A change to the model can
break a proof while `make lean` still passes, so `make books` is
never optional.

## Rules

1. **`books/Books/TypeSoundness/Checker/` imports nothing from `ruby-lean/RubyCore/`**,
   and nothing from the rest of its book. The checker and the model meet only in
   the proof around it.
2. **Only `validateD` is trusted.** Sorbet, the strippers, the desugarer and
   `emit_deriv.rb` are untrusted: a bug there may cost an accepted program and
   must never produce a wrongly accepted one. Never patch the checker to
   compensate for a bug upstream of it.
3. **The model declines; it does not approximate.** If a Ruby feature cannot be
   modeled faithfully, answer `unsupported` with a reason. A disagreement with
   CRuby is a bug.
4. **No `sorry`, no `native_decide`, no new axiom** in a proof.
5. **Recorded results only improve.** `difftest/coverage-baseline.json`,
   `desugar/coverage-baseline.json`, `books/corpus/accepted.txt` and each unit-test
   suite's `coverage-baseline.json` are compared on every run. Update one only
   with the command the check prints, in the same commit as the change that
   moved it, and never to hide a regression.
6. **Regenerate, do not edit, generated files** (`ruby-lean/RubyCore/Generated/`,
   `books/Books/TypeSoundness/Checker/Audit/`): `make gen`.
7. **Fix a lint finding; do not suppress it.** No `noqa`, `rubocop:disable`,
   `shellcheck disable` or test skip. New code in `desugar/`, `books/scripts/`
   or `difftest/` comes with unit tests, or its suite's coverage falls.
8. **Some files need the owner's review** (`.github/CODEOWNERS`): CI, the
   Makefile, `scripts/`, the lint and coverage configuration, the toolchain
   pins and the comparator's theorem statement. Keep changes to them in a pull
   request of their own.
9. **Documentation describes the present.** Put history in commit messages. Use
   names an outsider can read; do not introduce project-internal nicknames.

## Where things are

| Path | Contents |
|---|---|
| `ruby-lean/RubyCore/` | The model. Start at `RubyCore.lean` and `docs/semantics/index.md` |
| `books/Books/TypeSoundness/` | The type-soundness book: the theorem is in `Soundness.lean` |
| `books/Books/TypeSoundness/Checker/` | The type checker the theorem is about. Entry point `validateD` in `Check/` |
| `books/Books/Metatheory/` | Facts about the model |
| `books/Books/FastPower/`, `books/Books/Lib/` | A proof about one Ruby program, and the library for writing more |
| `books/corpus/` | Typed programs the checker is measured on |
| `desugar/` | Ruby to the model's core language |
| `difftest/` | Differential testing against CRuby |
| `docs/` | The documentation site |
