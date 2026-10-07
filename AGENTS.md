# AGENTS.md — ruby-lean

Start at [`README.md`](README.md): what this is, how to build it, and how to
reproduce every number. This file is the map for working *inside* it.

## Where the working record lives

Each area carries its own, and they are the real documentation — read the one
for what you are about to touch **before** touching it. The Lean work is two
Lake packages: `ruby-lean/` holds the model and the type checker, and `books/`
holds every proof about them, the corpus and the gate.

| Directory | Read first | Then |
|---|---|---|
| `ruby-lean/` (the model, `RubyCore/`) | [`ruby-lean/README.md`](ruby-lean/README.md) — layout, build; then [`docs/model/`](docs/model/fragment.md) for the fragment and metatheory | [`ruby-lean/RubyCore/README.md`](ruby-lean/RubyCore/README.md) — **the semantics itself**, and what code comments mean by *"artifact NN §M"*; then `ruby-lean/notes/model/implementation-notes.md`, `ruby-lean/notes/model/HANDOFF.md` |
| `ruby-lean/` (the checker, `Checker/`) | [`ruby-lean/Checker/README.md`](ruby-lean/Checker/README.md) — what the checker is and how it is laid out; then [`books/AGENTS.md`](books/AGENTS.md), which is the working record for the checker *and* its proof | as for `books/Books/TypeSoundness/` below |
| `books/` | [`books/README.md`](books/README.md) — the books, what each proves, the gate, the vocabulary, and where everything was before it moved here | each book's own README |
| `books/Books/TypeSoundness/` (the checker's soundness proof) | [`books/AGENTS.md`](books/AGENTS.md) — current state, the proof boundary, the pipeline, the gate; then its *Design record* for the Sorbet, reachability and answer-typed background the code cites | `books/notes/type-soundness/implementation-notes.md` (the chronological record), `found-issues.md` (open findings, §F-numbers), `HANDOFF.md` (the live resume point) |
| `books/Books/Metatheory/` (facts about the model) | [`books/Books/Metatheory/README.md`](books/Books/Metatheory/README.md); then [`docs/model/metatheory.md`](docs/model/metatheory.md) | `ruby-lean/notes/model/` |
| `books/Books/FastPower/`, `books/Books/Lib/` (proofs about one Ruby program) | [`books/Books/FastPower/README.md`](books/Books/FastPower/README.md) — how a program book is written and what the kernel can and cannot evaluate | `Books/Lib/` (the shared machinery) |
| `desugar/` | [`desugar/README.md`](desugar/README.md); then [`docs/front-end/`](docs/front-end/method.md) — the round-trip method (artifact 06), how the fragment grows, linearization | `implementation-choices.md` (C-numbers, cited from the code) |
| `difftest/` | [`difftest/README.md`](difftest/README.md); then [`docs/testing/`](docs/testing/engine.md) — the engine, its invariants, and the methodology (artifact 05) | `implementation-notes.md` (N-numbers, cited from the code) |
| `playground/` | [`playground/README.md`](playground/README.md) | [`docs/playground.md`](docs/playground.md) |
| `paper/` | [`paper/README.md`](paper/README.md) | — |

READMEs are short orientation pages. The longer design and methodology material
lives in `docs/`, an MkDocs site (see [`docs/index.md`](docs/index.md) for how to
build it). The written semantics (`ruby-lean/RubyCore/README.md`) and the working
notes stay next to their code. The cross-references the sources use
(*"artifact 02 §3"*, *"artifact 06 §4"*, *"types-and-preservation §A.5"*) resolve
into those files — see `books/AGENTS.md` §*Superseded design notes* for the
map, including which design documents were deleted and what they were.

## The one norm that matters

**The gate must be green before you commit.**

```sh
cd books && ./scripts/run_typed_ratchet.sh
```

Quiet mode is the default and is the right one; `--verbose` is for a failure
whose captured error was not enough. `RATCHET_SKIP_AGREEMENT=1` skips the CRuby
replay while iterating. In a sandbox with a protected uv cache, set
`UV_CACHE_DIR=/private/tmp/ruby-ratchet-uv-cache`.

GREEN does not mean finished — it means nothing is *started and incomplete*.
Rungs nobody has climbed are green, because nothing claims them. What is red is
the fragment claiming something the bridge cannot back. The default gate checks
soundness for enabled clinks and counts only actual `validateD` accepts as climbed.
`--clink-rebuild` checks proofs/controls only. The historical complete-coverage audit
(`--full-corpus`) is in `books/Unrebuilt/` with the unrebuilt proofs it reads.

## Two boundaries not to blur

1. **`Checker/` imports nothing from `RubyCore/`.** The checker carries its own
   copied `Expr`/`Ty`. The one place the two meet is the checker's soundness
   proof, `books/Books/TypeSoundness/`, which imports both — a denotation relates
   the two by definition — and it is in another package. The checker and the
   model share a Lake package, so the compiler does not refuse the import;
   `ruby-lean/scripts/check-isolation.sh` does, as the gate's first stage.
2. **Only `validateD` is trusted.** Sorbet, the strip stack, the desugarer and
   the derivation emitter are all untrusted by construction: they can cost an
   accept, never produce an unsound one. Keep it that way — if a fix is tempting
   to make inside the checker to rescue an emitter bug, it is the wrong fix.

## Proofs rot silently

No proof is on `ruby-lean/`'s build, so `lake build` there says nothing about
them: a change to the model or the checker can break a proof and leave that
package green. The gate rebuilds the soundness theorem and everything it
imports, which is most of `books/Books/Metatheory/` but not all of it. Run

```sh
make books        # every book
make proofs       # the metatheory's `#print axioms` and the heap measurements
```

at batch boundaries. Three independent breaks once sat undetected for 24 commits
because a green ratchet says nothing about the proofs it does not import. CI
builds every book on each pull request.
