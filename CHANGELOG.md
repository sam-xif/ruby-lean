# Changelog

## Unreleased

* One command, `make check`, runs every check: the build, every proof book, the
  axiom audits, the checker over its corpus, and the model against CRuby.
  Continuous integration runs the same targets and all of them block.
* `bin/ruby-lean` prints a program's output and value, and `--compare` runs it
  under CRuby as well. `bin/ruby-lean-check` type-checks one Sorbet-annotated
  program. `bin/new-book` starts a proof about a program, with a first theorem
  proved by the kernel.
* The model's sources are grouped: `Numeric/`, `Regex/`, `Generated/` and
  `Sorbet/` beside the semantics proper. Typing definitions that only proofs use
  moved to `books/Books/Metatheory/`.
* The set of corpus programs the checker accepts is recorded in
  `books/corpus/accepted.txt` and compared on every run.
* The documentation is a site (`make docs-serve`) organized by task.
* `make lint` formats and lints the Python (ruff), the Ruby tooling (RuboCop),
  the shell scripts (shellcheck) and the workflows (actionlint).
* Unit tests for the desugarer (`make desugar-unit`) and for the derivation
  emitter and signature reader (`make emitter-unit`). These suites and
  difftest's record their line and branch coverage, which may not fall.
* `make check-not-weakened`, and a pull-request check run from `main`'s copy,
  fail a change that weakens a check: a recorded result that fell, a dropped
  check or audited theorem, a new `sorry` or lint suppression, fewer tests.
  `.github/CODEOWNERS` lists the files that define the checks.

## 0.01

The first version that can be built from a clean checkout: the model, the
desugarer, the differential tester, the type checker and its soundness theorem.
