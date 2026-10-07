# `books/notes/` — the working record of the checker and its soundness proof

| Path | What it records |
|---|---|
| [`type-soundness/implementation-notes.md`](type-soundness/implementation-notes.md) | The chronological, clink-numbered record: what was tried, what broke, what it cost. |
| [`type-soundness/found-issues.md`](type-soundness/found-issues.md) | Open findings, §F-numbers — cited from live code. |
| [`type-soundness/HANDOFF.md`](type-soundness/HANDOFF.md) | The live resume point. |
| [`type-soundness/context-splitting.md`](type-soundness/context-splitting.md) | The `Ctx` redesign. |

The current state, not the history, is in [`../AGENTS.md`](../AGENTS.md).

**These files use the paths of the layout they were written in**, when the
checker was `ruby-lean/Ratchet/` and the proofs were `ruby-lean/Denote/` and
`ruby-lean/RubyCore/Proof/`: `Denote/Bridge.lean`, `Denote/Sem/Core/State.lean`,
`Ratchet/Check/Raw.lean`, `scripts/build_corpus.py`. The historical entries were
not rewritten. [`../README.md`](../README.md) §*Where things were before* has
the map to where each of those is now; `HANDOFF.md`, being live, uses the
current paths.

The model's own record is in `../../ruby-lean/notes/model/`.
