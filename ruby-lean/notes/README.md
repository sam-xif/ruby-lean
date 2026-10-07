# `ruby-lean/notes/` — the model's working record

| Path | What it records |
|---|---|
| [`model/implementation-notes.md`](model/implementation-notes.md) | The model (`RubyCore/`): the chronological L-numbered record — what was tried, what broke, what it cost. |
| [`model/HANDOFF.md`](model/HANDOFF.md) | The model's live resume point. |
| [`model/judgment-layer-implementation-notes.md`](model/judgment-layer-implementation-notes.md) | The J-numbered record of an earlier judgment layer, cited from `books/Books/Metatheory/Typing/Judge/`. |

The checker's record — the clink-numbered notes, the §F findings and its live
resume point — moved with its soundness proof to
[`../../books/notes/type-soundness/`](../../books/notes/type-soundness/). The two
records cite each other by clink/L-number, not by date.

**Backticked paths inside these files are relative to this package as it was
when they were written**, when it also held the proofs: `Denote/Bridge.lean`,
`RubyCore/Proof/HeapFacts.lean`, `scripts/build_corpus.py`, `Ratchet/…`. Those
have moved; [`../../books/README.md`](../../books/README.md) §*Where things were
before* has the map. Paths inside the historical narrative were not rewritten.

These files also cite the design documents that used to live in a central
`docs/` directory, by bare filename (`static-soundness-poc.md`,
`certificate-language.md`, `slot-frame.md`, …). That directory is gone: what was
still true was folded into the localized READMEs, and the rest was deleted.
[`../../books/AGENTS.md`](../../books/AGENTS.md) §*Superseded design notes* is the index — one line
per document on what it was — and the full text is in the git history.

The current state, not the history, is in [`../../books/AGENTS.md`](../../books/AGENTS.md) (the
checker), [`../README.md`](../README.md) (the package layout and build), [`../../docs/model/fragment.md`](../../docs/model/fragment.md) (what the model supports) and
[`../RubyCore/README.md`](../RubyCore/README.md) (the semantics itself).
