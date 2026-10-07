# Contributing

## Before you start

1. `scripts/check-prereqs.sh` — five tools, and the command to install whichever
   is missing.
2. Read [`AGENTS.md`](AGENTS.md). It names the working record for each directory
   and the two boundaries not to blur.
3. Read the `AGENTS.md` / `implementation-notes.md` of the directory you are
   about to change. They record what was already tried, including the things
   that did not work — the stall points are written down precisely so nobody
   pays for them twice.

## The rule

**The gate must be green before you commit:**

```sh
cd books && ./scripts/run_typed_ratchet.sh
```

RED means the certified fragment is claiming something the proofs cannot back —
an enabled rule with no semantic proof, a nonstandard axiom in soundness, a
failed control, or a pipeline/CRuby failure. Disabled rules are work remaining.
The default reports only enabled clinks and actual `validateD` accepts as climbed.
The historical complete-coverage audit is in `books/Unrebuilt/`.

GREEN with unclimbed rungs is the normal state. Ascent is ordinary work.

## What a good change looks like

* **Grow the fragment, don't widen the checker.** A new rule lands with its
  semantic proof (its *clink*) and admission to the `clinkEnabled` set in the same
  change: add its exact constructor suffix to
  `ruby-lean/Checker/ClinkPolicy.lean`'s `clinkProfile`, import its semantic provider
  in `books/Books/TypeSoundness/Registry/ActiveProofs.lean`, and enable the companion/body rules needed by its
  derivations. Climbing requires these proofs and controls to pass the active
  registry/soundness gate and the production `validateD` to accept the positive
  rung. A proved but gated rule remains unclimbed in the active ratchet. During
  semantic rebuilding, the default `./scripts/run_typed_ratchet.sh` from
  `books/` checks active soundness and corpus progress; `--clink-rebuild`
  checks proofs/controls only.
* **Keep the untrusted side untrusted.** If Sorbet, the strip stack, the
  desugarer or the emitter is wrong, fix it there. A patch inside `validateD` to
  rescue an upstream bug trades a false reject for a possible false accept, which
  is the one trade this design exists to refuse.
* **Add the negative control with the positive one.** Every accept should come
  with the nearby program that must still be rejected, `#guard`ed at build time.
* **Run the proofs at batch boundaries** — `make books`, and `make proofs` for the
  metatheory's axiom audit. The proofs are a separate Lake package (`books/`), so a
  green build of `ruby-lean/` says nothing about them and they will rot quietly otherwise.
* **Write the finding down.** `found-issues.md` (§F-numbers) and
  `implementation-notes.md` are part of the deliverable, not overhead.

## Corpus rungs

Rungs live in `books/corpus/NNN-id.rb` (annotated, the source of truth) beside
`NNN-id.meta.json` (what Sorbet and the checker are each expected to say).
`books/build/` is entirely derived — never edit it by hand.
