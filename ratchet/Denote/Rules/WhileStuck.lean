import Denote.Rules.VasgnStuck

/-!
# `Denote/Rules/WhileStuck.lean` — the second axis at a back edge *(TIMEBOXED MEASUREMENT)*

**Not a rung.** This file is a ~10-minute probe of `Judge.while'` on the stuck-freedom axis,
run straight after `VasgnStuck.lean` closed, to answer two questions the `vasgn` rung raised
and could not settle. Both are answered; the proof is deliberately **not** attempted.

## The machine cycle, read off `Interp/Kont.lean`

```
eval (while' c body) → withKont m (.eval c) (whileCondK c body)       -- Interp.lean:249
  … run c …
  deliver v to whileCondK:  truthy → withKont m (.eval body) (whileBodyK c body)
                            falsy  → withCtl m (.value .nil)          -- Kont.lean:165-167
  … run body …
  deliver w to whileBodyK → withKont m (.eval c) (whileCondK c body)  -- Kont.lean:168-169
```

The two konts **swap in place**: stack depth is constant, and the frame is never consumed.
That is the difference from `vasgn`, whose `asgnK` is pushed and popped once.

## Finding 1 — `stuckFreeRun_pushK` does not apply, and the reason is its fuel quantifier

Its delivery hypothesis is

    ∀ (v₀ m₀), … → ∀ f, typeStuck (run f (deliver m₀ v₀ K)) = false

quantified over **all** `f`. For `asgnK` that was free: the delivery is two steps and needs
no hypothesis. At a back edge the delivery *re-enters the loop*, so discharging it at
arbitrary `f` is discharging the very statement being proved. Circular.

The fix is visible and is `run_split`'s own shape: that lemma **exposes the split**
(`∃ n, …inner… ∧ ∃ f2, …delivery…`), so a caller can see the residual fuel. The stuck-axis
counterpart has to do the same and carry `f2 < fuel`. Note the bound is not free: in
`stuckFreeRun_pushK`'s `.value`/`kont = []` arm the delivery starts at the *same* fuel
(`pushK K m = deliver m w K` definitionally — zero steps consumed), so a decreasing variant
needs the "≥ 1 step" fact that holds for `eval c` and not in general.

**So the honest cost of `while'` is: one strengthened decomposition, then the rung.** Not a
`KontOk`, which is the second time this axis has failed to need one.

## Finding 2 — `JumpStuckFree` is not independently dischargeable here

`jumpStuckFree_asgnK` was four lines because `unwind`'s default arm pops the frame and hands
the jump back. `unwind` at a while kont (`Kont.lean:353-357`) does **not**:

    brkJ → .value v            -- exits, fine
    nxtJ → eval c, whileCondK  -- RE-ENTERS the loop
    redoJ → eval body, whileBodyK -- RE-ENTERS, skipping the condition

So two of the four arms are the loop again, and `JumpStuckFree [whileCondK c body]` is
mutually recursive with the rung. It has to be proved *inside* the same fuel induction, not
supplied to it as a side condition — which means the clean
`(CatchFree, JumpStuckFree, decomposition)` interface that fit `vasgn` does not factor here.

This is also where `found-issues.md` §F23 lives (a `next` escaping mid-body, fixed by
`nxtPrefixOk`), and it is not a coincidence: the `nxtJ` arm above is the very transition
that made that bug reachable.

## What the probe therefore concludes

Tractable, and bigger than a `vasgn`. The induction is on fuel (not syntax), it needs the
value axis for the back edge (`SemJudge body`'s `StateOk` conjunct is what says the next
iteration starts conformant — so the two ladders are *coupled* here, exactly as `vasgn` was
not), and it needs a fuel-decreasing decomposition that does not exist yet. Estimate by
analogy: the decomposition is a rewrite of `stuckFreeRun_pushK`'s 92 lines, the rung is
larger than `vasgn`'s 16 because of the two jump arms.

The obligation is stated below so the shape is on file and the premises are legible. It is
**not proved**, and nothing imports this file.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- The stuck-freedom obligation for `Judge.while'`, stated in the ladder's shape.

Four premises where `vasgn`'s had one, and the last two are the finding: an iteration may
only re-enter at a conformant machine, and the fact that it does is the **value** axis's
(`SemJudge`'s third conjunct). `Judge.while'`'s own `Γc = Γ`/`Ic = I`/`Γb = Γ`/`Ib = I`
premises are what make those two statable at the same `(κ, Γ, I)` the loop entered with —
i.e. the rule's fixed-point restriction *is* the loop invariant this proof would induct on,
and `Deriv.while' (Γl : Env) …` is where a certificate records it. -/
def OblStuck.Judge.while' : Prop :=
  ∀ (κ : Ctx) (Γ : Env) (I : Ty) (c body : Ratchet.Expr) (σ τ : Ty),
    -- the two stuck-freedom premises, as `vasgn` had for its right-hand side
    StuckFreeAt κ Γ I c →
    StuckFreeAt κ Γ I body →
    -- …and the two value-axis premises, which is the coupling: without them there is no
    -- reason the machine at the back edge still satisfies `StateOk κ Γ I`
    SemJudge κ Γ I c σ (κ.afterStmt c σ) Γ I →
    SemJudge κ Γ I body τ (κ.afterStmt body τ) Γ I →
    StuckFreeAt κ Γ I (.while' c body)

/-- The first step, for the record: entering the loop is one push, and the machine it turns
to is `evalFrom m c` under the loop's continuation — so the *entry* is `vasgn`'s shape
exactly. Everything after the first delivery is not. `rfl`. -/
theorem stepFn_while_push (m : Machine) (c body : Ratchet.Expr) :
    Interp.stepFn (evalFrom m (.while' c body))
      = .next (pushK [.whileCondK (toRuby c) (toRuby body)] (evalFrom m c)) := rfl

end Ratchet.Denote
