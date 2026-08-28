# HANDOFF — the slot frame (SF), 2026-08-28

Design: `../docs/semantics/slot-frame.md` (§10 lists the files). This note is the
*next-session* view: what is load-bearing, what is decoration until SF-T3, and
the proof plan for the one missing bridge.

## Built and green

`lake build Judgment Metatheory HJudge` all clean; `RubyCore.Proof.Static.Frame`
is axiom-clean (`propext`, `Quot.sound`, `Classical.choice`).

* **The algebra** — `Types/SlotClaim.lean`. `Holds` (Prop) / `holdsB` (kernel
  Bool) / `holdsB_iff`. `compose` concatenates with a `defined`-agreement guard.
* **The walk** — `Types/SlotWalk.lean`. Fuel-bounded, *not* `partial`, precisely
  so SF-T3 can induct over it.
* **SF-T1** `ResolvesAt_defineMethod_frame` / `_slot` — resolution survives a
  same-name `def` off the owned segment. The design's stated risk (that this
  would fight the shadow clause) did not materialize: `crubyShadow` reads only
  `className`.
* **SF-T2** `Holds_defineMethod` — a whole footprint framed by one
  non-conflicting write.
* **`holds_compose`** (composition is conjunction) and **`row_lookupIn`** (SF7's
  `Row` entails its resolution).
* **SF-T4's wire half** — `JCert.footprint`, `frameOkB` in `validateJ`.

## The one thing that is *not* proved, and must not be assumed

`frameOkB` passing does **not** yet imply a claim survives running the program.
Missing: *every `defineMethod` the machine performs while running `p` is one of
`installsOf p`'s enumerated installs.* Both endpoints exist (SF-T2 frames one
write; the walk enumerates the sites); the bridge is an induction over `stepFn`.

Until it lands the frame is **additive**: `validateJ_certifies` is still carried
by `declaresName`'s name-global guard, and adding `frameOkB` only strengthens
`validateJ`'s hypothesis, so every existing accept and every existing theorem is
untouched. The caveat is written into `frameOkB`'s docstring so it cannot be
read off the code as more than it is.

### Proof plan for the bridge (this is SF-T3's core)

1. State it as a step-level obligation: `stepFn` at a machine state whose control
   is a subterm of `p` either leaves the method tables alone, or performs a
   `defineMethod cls name md` for which `.defM (className cls) name ∈ installsOf p`.
2. The definee is the load-bearing coordinate: the walk tracks it lexically, the
   machine tracks it in the frame. Those two must be related — expect a lemma
   "the machine's definee at a subterm equals the walk's `definee` for that
   subterm", which is where `sclass`/`defs` being `opaque_` earns its keep.
3. With that, `Holds` preservation across `step` is SF-T2 plus the enumeration,
   and across `ReachableResult` it is the obvious induction.

Do **not** start by re-keying `Decls` rows per `(class, name)` (§7.1's
demolition). That is a large refactor whose payoff depends on this bridge; the
frame cannot replace `declaresName` before it can preserve a claim across a run.

## Smaller open items

* `bootResolver` knows boot classes only, so a footprint naming a
  program-declared class is rejected. SF9 says claims live at the conformant
  *start* state; resolving against the post-prefix heap is the fix.
* `defs` / `class << self` are `opaque_` (no eigenclass in the heap model), so a
  `defs`-bearing program needs a trivial footprint today.
* `Types/SlotClaimEg.lean` is the executable spec of the intended behaviour —
  §1's two measured blockers, SF8's table in both polarities, the walk on
  syntax. Extend it before changing semantics; every entry there is a `#guard`.
