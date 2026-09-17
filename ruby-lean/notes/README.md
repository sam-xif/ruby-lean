# `ruby-lean/notes/` — the working record

Two layers, two records, and they are kept separate because they were written
separately and cite each other by clink/L-number, not by date:

| Path | What it records |
|---|---|
| [`model/implementation-notes.md`](model/implementation-notes.md) | The model (`RubyCore/`): the chronological L-numbered record — what was tried, what broke, what it cost. |
| [`model/HANDOFF.md`](model/HANDOFF.md), [`model/HANDOFF-SF.md`](model/HANDOFF-SF.md) | The model's live resume points (the second is the slot-frame line of work). |
| [`model/v4-migration-handoff.md`](model/v4-migration-handoff.md) | The Lean 4 toolchain migration. |
| [`ratchet/implementation-notes.md`](ratchet/implementation-notes.md) | The checker (`Ratchet/`, `Semantics/`, `Denote/`): the clink-numbered record. |
| [`ratchet/found-issues.md`](ratchet/found-issues.md) | Open findings, §F-numbers — cited from live code. |
| [`ratchet/HANDOFF.md`](ratchet/HANDOFF.md) | The checker's live resume point. |
| [`ratchet/context-splitting.md`](ratchet/context-splitting.md) | The `Ctx` redesign. |

These files predate the merge of the `lean/` and `ratchet/` Lake packages into
this one. **Backticked paths inside them are relative to the package root**
(`ruby-lean/`) — `Denote/Typed/Bridge.lean`, `scripts/build_corpus.py`,
`RubyCore/Interp.lean`. Paths that named the old package layout were rewritten;
paths inside the historical narrative were not, so a sentence about "this
package" in an old entry may mean the checker's package as it then was.

These files also cite the design documents that used to live in a central
`docs/` directory, by bare filename (`static-soundness-poc.md`,
`certificate-language.md`, `slot-frame.md`, …). That directory is gone: what was
still true was folded into the localized READMEs, and the rest was deleted.
[`../AGENTS.md`](../AGENTS.md) §*Superseded design notes* is the index — one line
per document on what it was — and the full text is in the git history.

The current state, not the history, is in [`../AGENTS.md`](../AGENTS.md) (the
checker), [`../README.md`](../README.md) (the model's layout and build) and
[`../RubyCore/README.md`](../RubyCore/README.md) (the semantics itself).
