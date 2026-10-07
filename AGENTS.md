# AGENTS.md

Instructions for coding agents working in this repository. Human contributors:
see [`docs/contributing.md`](docs/contributing.md), which says the same at
greater length.

## Before you commit

```sh
make check
```

It must end with `make check: ALL CHECKS PASSED`. It builds the model and the
checker, builds every proof book, audits axioms, runs the checker over its
corpus, and runs the model against CRuby. Do not commit on a failure, do not
skip a failing target, and do not weaken a check to make it pass.

While iterating, run the narrower target for what you changed (`make help`
lists them), then `make check` once at the end:

| Changed | Run |
|---|---|
| `ruby-lean/RubyCore/`, `ruby-lean/prelude/` | `make conformance`, then `make books` |
| `ruby-lean/Checker/` | `make soundness` |
| `books/` | `make books` |
| `desugar/` | `make desugar-test desugar-coverage` |
| `difftest/` | `make difftest-test` |
| `docs/`, any README | `make docs` |

The proofs are a separate Lake package (`books/`). A change to the model or the
checker can break a proof while `make lean` still passes, so `make books` is
never optional.

## Rules

1. **`ruby-lean/Checker/` imports nothing from `ruby-lean/RubyCore/`.** The two
   meet only in `books/Books/TypeSoundness/`.
2. **Only `validateD` is trusted.** Sorbet, the strippers, the desugarer and
   `emit_deriv.rb` are untrusted: a bug there may cost an accepted program and
   must never produce a wrongly accepted one. Never patch the checker to
   compensate for a bug upstream of it.
3. **The model declines; it does not approximate.** If a Ruby feature cannot be
   modeled faithfully, answer `unsupported` with a reason. A disagreement with
   CRuby is a bug.
4. **No `sorry`, no `native_decide`, no new axiom** in a proof.
5. **Recorded results only improve.** `difftest/coverage-baseline.json`,
   `desugar/coverage-baseline.json` and `books/corpus/accepted.txt` are compared
   on every run. Update one only with the command the failing check prints, in
   the same commit as the change that moved it, and never to hide a regression.
6. **Regenerate, do not edit, generated files** (`ruby-lean/RubyCore/Generated/`,
   `ruby-lean/Checker/Audit/`): `make gen`.
7. **Documentation describes the present.** Put history in commit messages. Use
   names an outsider can read; do not introduce project-internal nicknames.

## Where things are

| Path | Contents |
|---|---|
| `ruby-lean/RubyCore/` | The model. Start at `RubyCore.lean` and `docs/semantics/index.md` |
| `ruby-lean/Checker/` | The type checker. Entry point `validateD` in `Check/` |
| `books/Books/TypeSoundness/` | The checker's soundness theorem, `Soundness.lean` |
| `books/Books/Metatheory/` | Facts about the model |
| `books/Books/FastPower/`, `books/Books/Lib/` | A proof about one Ruby program, and the library for writing more |
| `books/corpus/` | Typed programs the checker is measured on |
| `desugar/` | Ruby to the model's core language |
| `difftest/` | Differential testing against CRuby |
| `docs/` | The documentation site |
