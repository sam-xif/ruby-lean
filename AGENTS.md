# AGENTS.md

Instructions for coding agents working in this repository. Human contributors:
see [`docs/contributing.md`](docs/contributing.md), which says the same at
greater length.

## Before you commit

```sh
make check
```

It must end with `make check: ALL CHECKS PASSED`. It builds the model, builds
every proof book (the type checker is part of one), audits axioms, runs the checker over its
corpus, and runs the model against CRuby. Do not commit on a failure, do not
skip a failing target, and do not weaken a check to make it pass.

While iterating, run the narrower target for what you changed (`make help`
lists them), then `make check` once at the end:

| Changed | Run |
|---|---|
| `ruby-lean/RubyCore/`, `ruby-lean/prelude/` | `make conformance`, then `make books` |
| `books/Books/TypeSoundness/Checker/` | `make soundness` |
| anything else under `books/` | `make books` |
| `desugar/` | `make desugar-test desugar-coverage` |
| `difftest/` | `make difftest-test` |
| `docs/`, any README | `make docs` |

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
   `desugar/coverage-baseline.json` and `books/Books/TypeSoundness/corpus/accepted.txt` are compared
   on every run. Update one only with the command the failing check prints, in
   the same commit as the change that moved it, and never to hide a regression.
6. **Regenerate, do not edit, generated files** (`ruby-lean/RubyCore/Generated/`,
   `books/Books/TypeSoundness/Checker/Audit/`): `make gen`.
7. **Documentation describes the present.** Put history in commit messages. Use
   names an outsider can read; do not introduce project-internal nicknames.

## Where things are

| Path | Contents |
|---|---|
| `ruby-lean/RubyCore/` | The model. Start at `RubyCore.lean` and `docs/semantics/index.md` |
| `books/Books/TypeSoundness/` | The type-soundness book: the theorem is in `Soundness.lean` |
| `books/Books/TypeSoundness/Checker/` | The type checker the theorem is about. Entry point `validateD` in `Check/` |
| `books/Books/Metatheory/` | Facts about the model |
| `books/Books/FastPower/`, `books/Books/Lib/` | Two Ruby programs proved to meet one specification and compared, and the library for writing more |
| `books/Books/TypeSoundness/corpus/` | Typed programs the checker is measured on |
| `desugar/` | Ruby to the model's core language |
| `difftest/` | Differential testing against CRuby |
| `docs/` | The documentation site |
