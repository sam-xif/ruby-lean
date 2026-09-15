# AGENTS.md — ruby-lean

Start at [`README.md`](README.md): what this is, how to build it, and how to
reproduce every number. This file is the map for working *inside* it.

## Where the working record lives

Each area carries its own, and they are the real documentation — read the one
for what you are about to touch **before** touching it. The Lean work is one
Lake package (`ruby-lean/`) with two layers in it, and the record is split the
same way, under `ruby-lean/notes/`.

| Directory | Read first | Then |
|---|---|---|
| `ruby-lean/` (the checker, `Ratchet/`+`Denote/`) | [`ruby-lean/AGENTS.md`](ruby-lean/AGENTS.md) — current state, the proof boundary, the pipeline, the gate | `notes/ratchet/implementation-notes.md` (the chronological record), `notes/ratchet/found-issues.md` (open findings, §F-numbers), `notes/ratchet/HANDOFF.md` (the live resume point) |
| `ruby-lean/` (the model, `RubyCore/`) | [`ruby-lean/README.md`](ruby-lean/README.md) — layout, fragment, build | `notes/model/implementation-notes.md`, `notes/model/HANDOFF.md` |
| `difftest/` | [`difftest/README.md`](difftest/README.md) | `HANDOFF.md` |
| `playground/` | [`playground/README.md`](playground/README.md) | — |
| `docs/` | [`docs/README.md`](docs/README.md) | `docs/semantics/` in reading order |

## The one norm that matters

**The gate must be green before you commit.**

```sh
cd ruby-lean && ./scripts/run_typed_ratchet.sh
```

Quiet mode is the default and is the right one; `--verbose` is for a failure
whose captured error was not enough. `RATCHET_SKIP_AGREEMENT=1` skips the CRuby
replay while iterating. In a sandbox with a protected uv cache, set
`UV_CACHE_DIR=/private/tmp/ruby-ratchet-uv-cache`.

GREEN does not mean finished — it means nothing is *started and incomplete*.
Rungs nobody has climbed are green, because nothing claims them. What is red is
the fragment claiming something the bridge cannot back.

## Two boundaries not to blur

1. **`Ratchet/` imports nothing from `RubyCore/`.** The checker carries its own
   copied `Expr`/`Ty`. `Semantics/` is the single deliberate exception (it
   imports the real machine), and `Denote/` is the one library that imports
   both — a denotation relates the two by definition. Both layers share one Lake
   package now, so the compiler no longer refuses that import;
   `ruby-lean/scripts/check-isolation.sh` does, as the gate's first stage.
2. **Only `validateD` is trusted.** Sorbet, the strip stack, the desugarer and
   the derivation emitter are all untrusted by construction: they can cost an
   accept, never produce an unsound one. Keep it that way — if a fix is tempting
   to make inside the checker to rescue an emitter bug, it is the wrong fix.

## Proofs rot silently

`ruby-lean/RubyCore/Proof/` is off the default build target, and that is the right
call for build times and the wrong one for drift. Run

```sh
cd ruby-lean && ./scripts/check-proofs.sh      # builds the metatheory + `#print axioms`
```

at batch boundaries. Three independent breaks once sat undetected for 24 commits
because a green ratchet says nothing about the proofs.
