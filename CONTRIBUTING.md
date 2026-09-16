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
cd ruby-lean && ./scripts/run_typed_ratchet.sh
```

RED means the certified fragment is claiming something the proofs cannot back —
a rule with no semantic proof, a worked theorem about the wrong program, a
shrunk fragment, a moved floor. It is never something to work around; the floors
exist because a ratchet that can slip is not a ratchet.

GREEN with unclimbed rungs is the normal state. Ascent is ordinary work.

## What a good change looks like

* **Grow the fragment, don't widen the checker.** A new rule lands with its
  semantic proof (its *clink*) in the same change. A rule registered without one
  turns the gate red on purpose.
* **Keep the untrusted side untrusted.** If Sorbet, the strip stack, the
  desugarer or the emitter is wrong, fix it there. A patch inside `validateD` to
  rescue an upstream bug trades a false reject for a possible false accept, which
  is the one trade this design exists to refuse.
* **Add the negative control with the positive one.** Every accept should come
  with the nearby program that must still be rejected, `#guard`ed at build time.
* **Run the proofs at batch boundaries** — `cd ruby-lean && ./scripts/check-proofs.sh`.
  The metatheory is off the default build target and will rot quietly otherwise.
* **Write the finding down.** `found-issues.md` (§F-numbers) and
  `implementation-notes.md` are part of the deliverable, not overhead.

## Corpus rungs

Rungs live in `ruby-lean/corpus/NNN-id.rb` (annotated, the source of truth) beside
`NNN-id.meta.json` (what Sorbet and the checker are each expected to say).
`ruby-lean/build/` is entirely derived — never edit it by hand.
