import Denote.Rules.VasgnStuck
import Denote.Rules.WhileStuck

/-!
# `Denote/Rules/WhileStuck2.lean` — the loop, on the stuck-freedom axis

**Diagnosis**: `../../../docs/semantics/answer-typed-judgments.md` §2.3 — the false
`JumpStuckFree` below is one of the four walls that document traces to a single cause.

> **SUPERSEDED, 2026-09-11 — the two false hypotheses are gone.**
> `Denote/Rules/WhileAnswer.lean`'s `SemStuckA.Judge.while'` is this theorem **without**
> `hJc`/`hJb`, proved through the answer type (`Denote/Sem/Answer.lean`), together with a
> fully-discharged instance (`while 1; 2; end`) that this file cannot state. The §"What is
> still owed" refutation below is still true of `JumpStuckFree` and is the reason the
> interface changed; read it, then read `WhileAnswer.lean`'s header for what replaced it.
> Kept as the statement of record — it is the measurement that priced the change.

Follows `WhileStuck.lean`'s probe, which concluded that `stuckFreeRun_pushK` could not serve
a back edge because its delivery hypothesis was quantified over **all** fuel. That is fixed
(`stuckFreeRun_pushK_le`, `VasgnStuck.lean`), and this file spends the fix.

## The cycle, and where the fuel goes

```
pushK [condK] (evalFrom m c)          -- the loop machine; the statement is about this
  … cond's run, k+1 steps …           -- stuckFreeRun_pushK_le, f + k ≤ N
  deliver v₀ to condK       1 step    -- truthy → body; falsy → nil, exit
  … body's run, k'+1 steps …          -- stuckFreeRun_pushK_le again, f' + k' ≤ f-1
  deliver w to bodyK        1 step    -- the back edge: the loop machine again
```

so re-entry happens at `f' - 1 ≤ f - 2 ≤ N - 2`. **The two continuation deliveries are what
pay for the induction** — the sub-runs need not consume anything, which is why no "≥ 1 step"
lemma was needed after all (`WhileStuck.lean` §Finding 1 predicted one might be).

## What the two axes each contribute, visible in one place

The back edge needs the next iteration to start at a **conformant** machine, and that fact is
the *value* axis's: `SemJudge`'s third conjunct, available exactly when the sub-run returned
a value, which is exactly when the loop continues. Both `hcv` and `hbv` are used for nothing
else. This is the coupling `VasgnStuck.lean` did not have and predicted would appear here.

## What is still owed — and it is **false as stated**, which is the finding

`WhileStuck.lean` §Finding 2 said the two `JumpStuckFree`s were mutually recursive with this
theorem and needed interleaved inductions. That was too kind. Reading `unwind`'s while arms
(`Interp/Kont.lean:353-357`):

```
brkJ v → .value v                     -- exits; safe
nxtJ _ → withKont m (.eval c)    condK -- = the loop machine at m
redoJ  → withKont m (.eval body) bodyK -- = the loop machine at m, skipping the condition
_      → withCtl  m (.jump j)          -- pass-through; the hypothesis covers it
```

The `nxtJ` and `redoJ` arms re-enter the loop **at `m`**, and re-entering needs
`StateOk κ Γ I m`. `JumpStuckFree` carries no such hypothesis — by design, because
`jumpStuckFree_asgnK` did not need one: `asgnK` hands the jump *back*, so the condition can
be machine-agnostic.

So `JumpStuckFree [.whileCondK c body]` is not a lemma waiting to be proved. It is **false**,
and the counterexample is concrete: take `m` whose locals disagree with `Γ` (say `x` holds a
`String` where `Γ` says `Integer`), `m.ctl = .jump (.nxtJ .nil)`, `m.kont = []`. Its own run
escapes to `.stuck`, so `typeStuck` is `false` at every fuel and the hypothesis holds — while
`pushK [condK] m` re-enters the loop at a non-conformant machine, where `c` can be `x + 1`
and genuinely type-stuck.

**The repair is an interface change, not a proof**: the jump side condition has to carry the
typing context, i.e. read `StateOk κ Γ I m → …` rather than quantifying over machines whose
only property is that their own run is safe. And that is the first place on this axis where an
*intermediate* machine has to be described by the typing context — which is what a `KontOk`
is. Two rungs went by without needing one (`VasgnStuck.lean`, and everything above this
paragraph); the boundary is **a continuation a jump can re-enter**.

-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The two deliveries, as step lemmas -/

theorem catchFree_whileCondK (c body : RubyCore.Expr) :
    RubyCore.Proof.CatchFree [.whileCondK c body] := by
  intro k hk t
  rcases List.mem_singleton.mp hk with rfl
  simp

theorem catchFree_whileBodyK (c body : RubyCore.Expr) :
    RubyCore.Proof.CatchFree [.whileBodyK c body] := by
  intro k hk t
  rcases List.mem_singleton.mp hk with rfl
  simp

/-- A truthy condition enters the body, under the loop's *other* continuation. -/
theorem stepFn_condK_true {m₀ : Machine} {v₀ : Value} {c body : RubyCore.Expr}
    (h : v₀.truthy = true) :
    Interp.stepFn (deliver m₀ v₀ [.whileCondK c body])
      = .next { m₀ with ctl := .eval body, kont := [.whileBodyK c body] } := by
  simp [Interp.stepFn, Interp.applyKont, Interp.withKont, h]

/-- A falsy condition exits, at `nil` and an empty continuation — two steps from done. -/
theorem stepFn_condK_false {m₀ : Machine} {v₀ : Value} {c body : RubyCore.Expr}
    (h : v₀.truthy = false) :
    Interp.stepFn (deliver m₀ v₀ [.whileCondK c body])
      = .next { m₀ with ctl := .value .nil, kont := [] } := by
  simp [Interp.stepFn, Interp.applyKont, Interp.withCtl, h]

/-- **The back edge.** `rfl`: delivering the body's value to `whileBodyK` is the loop
machine again, with the condition to re-evaluate. -/
theorem stepFn_bodyK (m₁ : Machine) (w : Value) (c body : RubyCore.Expr) :
    Interp.stepFn (deliver m₁ w [.whileBodyK c body])
      = .next { m₁ with ctl := .eval c, kont := [.whileCondK c body] } := rfl

/-- The exit is stuck-free: a value at an empty continuation is one step from `.done`. -/
theorem exit_stuckFree (m₀ : Machine) :
    ∀ f, Semantics.typeStuck
      (Interp.run f ({ m₀ with ctl := .value .nil, kont := [] } : Machine)) = false := by
  intro f
  match f with
  | 0 => simp [Interp.run, Semantics.typeStuck]
  | f + 1 => simp [Interp.run, Interp.stepFn, Interp.applyKont, Semantics.typeStuck]

/-! ## The loop -/

/-- **`Judge.while'` on the stuck-freedom axis, modulo the two jump conditions.**

The induction is on **fuel**, not on syntax — the first rung on either axis for which that
is true, and the reason the loop is not a `vasgn`. `ih` is consumed at exactly one place:
the back edge. -/
theorem loop_stuck_of_jumps {κ : Ctx} {Γ : Env} {I : Ty} {c body : Ratchet.Expr} {σ τ : Ty}
    (hc : StuckFreeAt κ Γ I c) (hb : StuckFreeAt κ Γ I body)
    (hcv : SemJudge κ Γ I c σ (κ.afterStmt c σ) Γ I)
    (hbv : SemJudge κ Γ I body τ (κ.afterStmt body τ) Γ I)
    (hJc : JumpStuckFree [.whileCondK (toRuby c) (toRuby body)])
    (hJb : JumpStuckFree [.whileBodyK (toRuby c) (toRuby body)]) :
    ∀ (N : Nat) (fuel : Nat), fuel ≤ N → ∀ m : Machine, StateOk κ Γ I m →
      Semantics.typeStuck (Interp.run fuel
        (pushK [.whileCondK (toRuby c) (toRuby body)] (evalFrom m c))) = false := by
  intro N
  induction N with
  | zero =>
    intro fuel hle m _
    have h0 : fuel = 0 := Nat.le_zero.mp hle
    subst h0
    simp [Interp.run, Semantics.typeStuck]
  | succ N ih =>
    intro fuel _ m hm
    -- the condition's sub-run, with the fuel bound the back edge will spend
    refine stuckFreeRun_pushK_le _ (catchFree_whileCondK _ _) hJc fuel (evalFrom m c)
      (hc m hm) ?_
    intro k v₀ m₀ hval f hle
    -- the value axis: the condition left the machine conformant
    have hSt₀ : StateOk κ Γ I m₀ := (hcv.2 m hm v₀ m₀ ⟨k + 1, hval⟩).2.2.1
    match f with
    | 0 => simp [Interp.run, Semantics.typeStuck]
    | f1 + 1 =>
      rw [Interp.run]
      by_cases htr : v₀.truthy = true
      · -- truthy: into the body, under `whileBodyK`
        rw [stepFn_condK_true htr]
        -- the machine the condK arm produces **is** `pushK [bodyK] (evalFrom m₀ body)`,
        -- definitionally, so the application needs no rewrite
        refine stuckFreeRun_pushK_le _ (catchFree_whileBodyK _ _) hJb f1
          (evalFrom m₀ body) (hb m₀ hSt₀) ?_
        intro k' w m₁ hval' f' hle'
        have hSt₁ : StateOk κ Γ I m₁ := (hbv.2 m₀ hSt₀ w m₁ ⟨k' + 1, hval'⟩).2.2.1
        match f' with
        | 0 => simp [Interp.run, Semantics.typeStuck]
        | f2 + 1 =>
          -- **the back edge**, and the only use of the induction hypothesis
          rw [Interp.run, stepFn_bodyK]
          exact ih f2 (by omega) m₁ hSt₁
      · -- falsy: the loop exits at `nil`
        rw [stepFn_condK_false (by simpa using htr)]
        exact exit_stuckFree m₀ f1

/-- The obligation's shape, discharged from the above at `N = fuel`. -/
theorem SemStuck.Judge.while_of_jumps {κ : Ctx} {Γ : Env} {I : Ty}
    {c body : Ratchet.Expr} {σ τ : Ty}
    (hc : StuckFreeAt κ Γ I c) (hb : StuckFreeAt κ Γ I body)
    (hcv : SemJudge κ Γ I c σ (κ.afterStmt c σ) Γ I)
    (hbv : SemJudge κ Γ I body τ (κ.afterStmt body τ) Γ I)
    (hJc : JumpStuckFree [.whileCondK (toRuby c) (toRuby body)])
    (hJb : JumpStuckFree [.whileBodyK (toRuby c) (toRuby body)]) :
    StuckFreeAt κ Γ I (.while' c body) := by
  intro m hm fuel
  match fuel with
  | 0 => simp [evalFrom, Interp.run, Semantics.typeStuck]
  | f + 1 =>
    rw [Interp.run, stepFn_while_push]
    exact loop_stuck_of_jumps hc hb hcv hbv hJc hJb f f (Nat.le_refl f) m hm

#print axioms SemStuck.Judge.while_of_jumps

end Ratchet.Denote
