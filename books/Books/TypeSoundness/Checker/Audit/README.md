# Audited checker sources (generated, not committed)

Every `*.lean` file in this directory is a **build output** produced by
`books/scripts/generate_audited_checker.py` from the checker in `../Check/`
(it rewrites each module's imports and namespace into the `Checker.Audit`
copy the soundness proof audits against the real registry). They are **not**
committed (see the repository `.gitignore`); do not edit or commit them.

`make gen` writes them, and the build targets that compile the books depend on
that step, so `make books` / `make soundness` / `make check` regenerate them
first. In a fresh checkout with no prior `make`, run `make gen` once (it needs
Python) before building the books directly.

Do not edit these; change `../Check/` and regenerate.
