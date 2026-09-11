import Denote.Sem.SafeKont
import Denote.Rules.WhileStuck2

/-!
# `Denote/Rules/WhileAnswer.lean` — the loop, unconditionally

**The wall this file removes**: `../../../docs/semantics/answer-typed-judgments.md` §2.3 and
`Denote/Rules/WhileStuck2.lean`'s header. That file proves `Judge.while'` on the
stuck-freedom axis **modulo two hypotheses that are false**:

    hJc : JumpStuckFree [.whileCondK …]      -- refuted in WhileStuck2.lean's header
    hJb : JumpStuckFree [.whileBodyK …]

`JumpStuckFree K` quantifies over every machine whose *own* run is stuck-free and claims the
same of the machine under `K`. At a loop continuation that is false, because `unwind`'s
`nxtJ` and `redoJ` arms **re-enter the loop at `m`**, and re-entry needs `StateOk κ Γ I m`,
which the side condition has no way to carry.

Under the answer type the side condition does not exist. The escape is an `Answer`, so it
arrives at the continuation *together with* whatever the premise says about the machine it
escaped from — and a premise that says `StateOk` is exactly what the two re-entering arms
need. The wall was an artefact of stating the fact about escapes in a place where the
machine's description was not in scope.

## What the rung costs now

Four premises, all satisfiable:

| premise | what it is |
|---|---|
| `StuckFreeAt κ Γ I c` / `… body` | as before — the sub-expressions do not get stuck |
| `AnswerOkAt κ Γ I c` / `… body` | **new, and this is the content**: every answer the sub-expression delivers leaves the machine conformant |

`AnswerOkAt` is strictly stronger than the `SemJudge` conjunct `WhileStuck2.lean` used, and
the extra strength is the `esc` arm: *the invariant holds at a `next`/`redo` too*, not only
at a normal exit. That is a genuine proof obligation on a loop body — `while (x = "s"; next)`
falsifies it — and the value ladder could not state it (§2.1: a raising or jumping run never
reaches `.value`, so no obligation of `SemJudge`'s shape can say anything about it).

So the ledger is: **two false hypotheses out, one true and necessary one in.**

## The induction

On fuel, as before, but the two loop entry points are proved **together** — the `redoJ` arm
re-enters at the body while the `nxtJ` arm re-enters at the condition, so a statement about
one alone is not closed under its own unwinding. `runA_rest_le` is what makes the measure
decrease: the answer point is reached with strictly less fuel than the delivery that follows
it, and the two continuation deliveries pay the remaining step each.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The new premise -/

/-- **Every answer `e` delivers leaves the machine conformant.**

The `val` arm of this is `SemJudge`'s third conjunct at `Γ' = Γ`, `I' = I` — what
`WhileStuck2.lean` consumed. The `esc` arm is new and is the one the loop's back edge needs;
it has no counterpart on the value axis, by construction. -/
def AnswerOkAt (κ : Ctx) (Γ : Env) (I : Ty) (e : Ratchet.Expr) : Prop :=
  ∀ m : Machine, StateOk κ Γ I m →
    Delivers (evalFrom m e) (fun _ m₀ => StateOk κ Γ I m₀)

theorem delivers_and {m : Machine} {P Q : Answer → Machine → Prop}
    (hP : Delivers m P) (hQ : Delivers m Q) :
    Delivers m (fun a m₀ => P a m₀ ∧ Q a m₀) :=
  fun fuel a m₀ rest h => ⟨hP fuel a m₀ rest h, hQ fuel a m₀ rest h⟩

/-! ## `unwind` at a while continuation, as a function

Both while konts take the same `unwind` arm (`Interp/Kont.lean:353`, a two-pattern match), so
one successor function serves both and the two step lemmas are the same `cases j <;> rfl`. -/

/-- Where a jump delivered to a while continuation goes. The frame is popped first
(`unwind`'s `let m := { m with kont := rest }`), so every arm names an empty continuation
except the two that re-enter. -/
def whileUnwind (m₀ : Machine) (c body : RubyCore.Expr) : Jump → Machine
  | .brkJ v => { m₀ with ctl := .value v, kont := [] }
  | .nxtJ _ => { m₀ with ctl := .eval c, kont := [.whileCondK c body] }
  | .redoJ => { m₀ with ctl := .eval body, kont := [.whileBodyK c body] }
  | .raiseJ exc => { m₀ with ctl := .jump (.raiseJ exc), kont := [] }
  | .retJ v t => { m₀ with ctl := .jump (.retJ v t), kont := [] }
  | .retryJ => { m₀ with ctl := .jump .retryJ, kont := [] }
  | .throwJ t v => { m₀ with ctl := .jump (.throwJ t v), kont := [] }

theorem stepFn_condK_jump (m₀ : Machine) (c body : RubyCore.Expr) (j : Jump) :
    Interp.stepFn (deliverA (.esc j) m₀ [.whileCondK c body])
      = .next (whileUnwind m₀ c body j) := by
  cases j <;> rfl

theorem stepFn_bodyK_jump (m₀ : Machine) (c body : RubyCore.Expr) (j : Jump) :
    Interp.stepFn (deliverA (.esc j) m₀ [.whileBodyK c body])
      = .next (whileUnwind m₀ c body j) := by
  cases j <;> rfl

/-! ## The loop -/

/-- **Both entry points, together.** `.1` is "the loop, about to evaluate its condition";
`.2` is "the loop, about to evaluate its body". `redoJ` turns the first into the second and
`nxtJ` turns the second into the first, so neither is provable alone. -/
theorem loop_stuck {κ : Ctx} {Γ : Env} {I : Ty} {c body : Ratchet.Expr}
    (hc : StuckFreeAt κ Γ I c) (hb : StuckFreeAt κ Γ I body)
    (hca : AnswerOkAt κ Γ I c) (hba : AnswerOkAt κ Γ I body) :
    ∀ (N fuel : Nat), fuel ≤ N → ∀ m : Machine, StateOk κ Γ I m →
      Semantics.typeStuck (Interp.run fuel
        (pushK [.whileCondK (toRuby c) (toRuby body)] (evalFrom m c))) = false ∧
      Semantics.typeStuck (Interp.run fuel
        (pushK [.whileBodyK (toRuby c) (toRuby body)] (evalFrom m body))) = false := by
  intro N
  induction N with
  | zero =>
    intro fuel hle m _
    have h0 : fuel = 0 := Nat.le_zero.mp hle
    subst h0
    exact ⟨by simp [run_zero, Semantics.typeStuck], by simp [run_zero, Semantics.typeStuck]⟩
  | succ N ih =>
    intro fuel hle m hm
    constructor
    · -- **the condition entry**
      refine safe_pushK_le (N := N + 1) (catchFree_whileCondK _ _) haltBlind_stuck oof_stuck
        (hc m hm) (delivers_and (hca m hm) (delivers_safeA (hc m hm))) ?_ fuel hle
      rintro a m₀ rest ⟨hok, hesc⟩ hrest
      match rest with
      | 0 => simp [run_zero, Semantics.typeStuck]
      | r + 1 =>
        rw [run_succ]
        cases a with
        | val v =>
          by_cases htr : v.truthy = true
          · rw [deliverA_val, stepFn_condK_true (m₀ := m₀) (v₀ := v) htr]
            exact (ih r (by omega) m₀ hok).2
          · rw [deliverA_val, stepFn_condK_false (m₀ := m₀) (v₀ := v) (by simpa using htr)]
            exact exit_stuckFree m₀ r
        | esc j =>
          rw [stepFn_condK_jump]
          cases j with
          | brkJ v => exact safeA_value_nil m₀ v r
          | nxtJ w => exact (ih r (by omega) m₀ hok).1
          | redoJ => exact (ih r (by omega) m₀ hok).2
          | raiseJ exc => exact hesc r
          | retJ v t => exact hesc r
          | retryJ => exact hesc r
          | throwJ t v => exact hesc r
    · -- **the body entry**
      refine safe_pushK_le (N := N + 1) (catchFree_whileBodyK _ _) haltBlind_stuck oof_stuck
        (hb m hm) (delivers_and (hba m hm) (delivers_safeA (hb m hm))) ?_ fuel hle
      rintro a m₀ rest ⟨hok, hesc⟩ hrest
      match rest with
      | 0 => simp [run_zero, Semantics.typeStuck]
      | r + 1 =>
        rw [run_succ]
        cases a with
        | val v =>
          rw [deliverA_val, stepFn_bodyK m₀ v (toRuby c) (toRuby body)]
          exact (ih r (by omega) m₀ hok).1
        | esc j =>
          rw [stepFn_bodyK_jump]
          cases j with
          | brkJ v => exact safeA_value_nil m₀ v r
          | nxtJ w => exact (ih r (by omega) m₀ hok).1
          | redoJ => exact (ih r (by omega) m₀ hok).2
          | raiseJ exc => exact hesc r
          | retJ v t => exact hesc r
          | retryJ => exact hesc r
          | throwJ t v => exact hesc r

/-- **The rung.** `Judge.while'` on the stuck-freedom axis, with no unproved and no false
side condition. Compare `SemStuck.Judge.while_of_jumps`, which is this statement plus `hJc`
and `hJb`. -/
theorem SemStuckA.Judge.while' {κ : Ctx} {Γ : Env} {I : Ty} {c body : Ratchet.Expr}
    (hc : StuckFreeAt κ Γ I c) (hb : StuckFreeAt κ Γ I body)
    (hca : AnswerOkAt κ Γ I c) (hba : AnswerOkAt κ Γ I body) :
    StuckFreeAt κ Γ I (.while' c body) := by
  intro m hm fuel
  match fuel with
  | 0 => simp [evalFrom, run_zero, Semantics.typeStuck]
  | f + 1 =>
    rw [run_succ, stepFn_while_push]
    exact (loop_stuck hc hb hca hba f f (Nat.le_refl f) m hm).1

/-! ## Non-vacuity

`WhileStuck2.lean` could not exhibit a single loop, because both of its jump hypotheses are
false and nothing discharges them. Here the leaf premise is two lines and the loop is
unconditional. -/

/-- The `AnswerOkAt` counterpart of `stuckFree_pure`: an expression that steps straight to a
value at the empty continuation delivers exactly one answer, at a machine that differs from
the one it started at only in the frame. -/
theorem answerOk_pure {κ : Ctx} {Γ : Env} {I : Ty} {e : Ratchet.Expr} {w : Value}
    (hstep : ∀ m : Machine, Interp.stepFn (evalFrom m e) = .next (reCtl m (.value w) [])) :
    AnswerOkAt κ Γ I e := by
  intro m hm fuel a m₀ rest hr
  have hap : answerPoint (evalFrom m e) = none := rfl
  match fuel with
  | 0 => rw [runA_zero hap] at hr; exact absurd hr (by simp)
  | f + 1 =>
    rw [runA_succ hap] at hr
    simp only [hstep m] at hr
    have hap2 : answerPoint (reCtl m (.value w) []) = some (.val w) := rfl
    rw [runA_ans hap2] at hr
    injection hr with h1 h2 h3
    subst h2
    exact StateOk_reCtl hm (.value w) []

theorem answerOk_intLit (κ : Ctx) (Γ : Env) (I : Ty) (n : Int) :
    AnswerOkAt κ Γ I (.int n) :=
  answerOk_pure (w := .int n) (fun _ => rfl)

/-- **`while 1; 2; end` reaches no type-stuck outcome, from any conformant machine** — with
every hypothesis discharged. This is the statement `WhileStuck2.lean` cannot make. -/
example (κ : Ctx) (Γ : Env) (I : Ty) :
    StuckFreeAt κ Γ I (.while' (.int 1) (.int 2)) :=
  SemStuckA.Judge.while'
    (SemStuck.Judge.intLit κ Γ I 1) (SemStuck.Judge.intLit κ Γ I 2)
    (answerOk_intLit κ Γ I 1) (answerOk_intLit κ Γ I 2)

#print axioms SemStuckA.Judge.while'
#print axioms loop_stuck

end Ratchet.Denote
