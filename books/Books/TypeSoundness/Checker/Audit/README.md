# The audited checker

This directory mixes hand-written sources with generated ones.

**Hand-written, committed:** `Derive.lean`, `Erase.lean` and `Permissions.lean`.
Edit these like any other source.

**Generated, not committed:** every module listed in `MODULES` in
`books/scripts/generate_audited_checker.py` (`python3
books/scripts/generate_audited_checker.py --list` prints them). The generator
rewrites each from the same-named module in `../Check/`, changing its imports
and namespace into the `Checker.Audit` copy that the soundness proof audits
against the real registry. Each starts with a `-- Generated from` line. Do not
edit them: change `../Check/` and regenerate.

The generated modules are listed one by one in the repository `.gitignore`.
`make gen-check` fails if a generated module is committed, or if that list and
the generator's differ. `make gen` writes them, and every target that builds the
checker or the books regenerates them first. In a fresh checkout with no prior
`make`, run `make gen` once (it needs Python) before building the books directly.
