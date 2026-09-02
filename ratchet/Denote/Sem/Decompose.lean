import Denote.Sem.Judge
import RubyCore.Proof.KontFrameStep
import RubyCore.Proof.NotDone

/-!
# `Denote/Sem/Decompose.lean` — the fifth stall point, cleared

`Denote/Sem/Frame.lean` states the interpreter's frame rule (`KontFrameCatchFree`) and the
decomposition the compound rungs need (`EvalsDecompose`), and states them as *unproved
propositions* — with a refutation of the naive version and a measurement of the corrected
one's cost. This file consumes the proofs, which live where that file said they belong:
`RubyCore/Proof/KontFrame*.lean`, next to `stepFn`.

## What the proofs actually say

`RubyCore.Proof.stepFn_frame` is the frame rule, with the two hypotheses the ratchet's
statement predicted (`CatchFree K`) and half-predicted (the side condition — see below):

    CatchFree K → (m.kont ≠ [] ∨ ∃ e, m.ctl = .eval e) → stepFn m = .next m₂ →
      stepFn (pushK K m) = .next (pushK K m₂)

`RubyCore.Proof.done_inv` is the inversion that makes a *run* decomposable: `.done` is
constructed at one site in the whole interpreter (`applyKont`'s empty-continuation arm) and
`applyKont` is called from one place (`stepFn`), so

    stepFn m = .done v m'  →  m.ctl = .value v ∧ m.kont = [] ∧ m' = m

which is what identifies the state a sub-run *ends at* — and hence the state the outer run
passes through.

## The third hypothesis, and it is not bookkeeping

`JumpOpaque K` below: the appended continuation cannot turn an escaping jump into a returned
value. Without it the decomposition is false, and `Frame.lean` already has the Ruby
counterexample (a `throw` caught outside, whose `begin` block returns 1 under the empty
continuation and escapes entirely under the enclosing `catch`). `CatchFree` handles that one;
`JumpOpaque` handles the rest of the family — a `rescue` in `K` catching what the sub-run
raised, a `whileBodyK` in `K` swallowing a `break`. It holds by computation for every
continuation a `Judge` rule pushes, because those are literals.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The bridge

`Denote/Sem/Frame.lean` defines `pushK` and `CatchFree` independently of
`RubyCore/Proof/`'s — deliberately, so the statement of the wall could be written before the
proof existed. They are the same functions, and these two `rfl`s are the whole cost of having
had both. -/

theorem pushK_eq (K : List Kont) (m : Machine) : pushK K m = RubyCore.Proof.pushK K m := rfl

theorem catchFree_iff (K : List Kont) : CatchFree K ↔ RubyCore.Proof.CatchFree K := Iff.rfl

/-! ## `JumpOpaque` -/

/-- The appended continuation cannot turn an escaping jump into a returned value. -/
def JumpOpaque (K : List Kont) : Prop :=
  ∀ (m : Machine) (j : Jump) (fuel : Nat) (v : Value) (m' : Machine),
    Interp.run fuel { m with ctl := .jump j, kont := K } ≠ .value v m'

/-! ## Discharging `JumpOpaque`

For the continuations a `Judge` rule pushes — all literals — `JumpOpaque` follows from one
general fact plus one computation per kont. The general fact is that **a jump at an empty
continuation never returns a value**: `unwind []` either escapes (`.uncaught` on a raise,
`.stuck` on a `break`/`next`/`retry`) or steps to a `raiseErr`, which is itself a jump at the
same empty continuation one step later. -/

/-- A machine whose control word is a jump and whose continuation is empty never returns a
value, at any fuel. The `retJ` and `throwJ` arms are why this is an induction rather than a
computation: both *step*, to a `raiseErr` — and `raiseErr` leaves the continuation alone, so
the next state is of the same shape. -/
theorem jump_empty_never_value :
    ∀ (fuel : Nat) (m : Machine) (j : Jump) (v : Value) (m' : Machine),
      m.ctl = .jump j → m.kont = [] → Interp.run fuel m ≠ .value v m' := by
  intro fuel
  induction fuel with
  | zero => intro m j v m' _ _ h; simp only [Interp.run] at h
  | succ n ih =>
    intro m j v m' hc hk h
    rw [Interp.run, Interp.stepFn, hc, Interp.unwind.eq_def, hk] at h
    cases j with
    | raiseJ exc => simp only at h
    | retJ w target =>
      -- `raiseErr` keeps the continuation, so the successor is a jump at `[]` again
      simp only at h
      exact ih _ (.raiseJ _) v m' rfl (by simp [Interp.raiseErr]) h
    | throwJ tag w =>
      simp only at h
      split at h
      · exact ih _ (.raiseJ _) v m' rfl (by simp [Interp.raiseErr]) h
      · simp only at h
    | brkJ w => simp only at h
    | nxtJ w => simp only at h
    | redoJ => simp only at h
    | retryJ => simp only at h

/-- `[.asgnK kind x]` is jump-opaque: `unwind`'s default arm passes the jump straight through
with the frame popped, which lands on `jump_empty_never_value`. This is the continuation
`Judge.vasgn` pushes, and the shape every other rule's literal kont will follow. -/
theorem jumpOpaque_asgnK (kind : VarKind) (x : String) :
    JumpOpaque [.asgnK kind x] := by
  intro m j fuel v m' h
  match fuel with
  | 0 => simp only [Interp.run] at h
  | f + 1 =>
    rw [Interp.run] at h
    have hs : Interp.stepFn { m with ctl := .jump j, kont := [.asgnK kind x] }
        = .next (Interp.withCtl { m with ctl := .jump j, kont := [] } (.jump j)) := rfl
    rw [hs] at h
    exact jump_empty_never_value f _ j v m' rfl rfl h

/-! ## The decomposition -/

/-- The delivery state: the machine a sub-run ends at, seen from outside — its own value in
flight, and the outer continuation still to go. -/
abbrev deliver (m : Machine) (v : Value) (K : List Kont) : Machine :=
  { m with ctl := .value v, kont := K }

/-- At an empty continuation with a value in flight, `pushK K` *is* the delivery state. This
is the pass-through point, and it is a `rfl`. -/
theorem pushK_eq_deliver {m : Machine} {w : Value} (hc : m.ctl = .value w)
    (hk : m.kont = []) : pushK K m = deliver m w K := by
  simp only [pushK, deliver, hk, List.nil_append, ← hc]

/-- **The run-level frame rule.** A run under an appended continuation `K` splits at the state
that delivers the inner run's value to `K`: the inner run returns, and the outer run continues
from the delivery state.

Both existentials are honest. The inner run's fuel is not the outer one's — the outer run
spends the same steps and then keeps going — and that is exactly why `Evals`, which quantifies
its own fuel existentially, is the right shape to receive this. -/
theorem run_split (K : List Kont) (hK : RubyCore.Proof.CatchFree K) (hJ : JumpOpaque K) :
    ∀ (fuel : Nat) (m : Machine) (v : Value) (m' : Machine),
      Interp.run fuel (pushK K m) = .value v m' →
      ∃ (n : Nat) (v₀ : Value) (m₀ : Machine),
        Interp.run n m = .value v₀ m₀ ∧
        ∃ f2, Interp.run f2 (deliver m₀ v₀ K) = .value v m' := by
  intro fuel
  induction fuel with
  | zero => intro m v m' h; simp only [Interp.run] at h
  | succ n ih =>
    intro m v m' h0
    have h := h0
    rw [Interp.run] at h
    cases hc : m.ctl with
    | eval e =>
      -- `evalExpr` never reads the continuation, so the frame rule needs no side condition
      have hstep : Interp.stepFn (pushK K m) =
          RubyCore.Proof.frameR K (Interp.stepFn m) := by
        simp only [Interp.stepFn, pushK_eq, RubyCore.Proof.pushK_ctl, hc,
          RubyCore.Proof.evalExpr_frame K hK]
      rw [hstep] at h
      cases hev : Interp.stepFn m with
      | next m₂ =>
        rw [hev] at h
        simp only [RubyCore.Proof.frameR] at h
        obtain ⟨k, v₀, m₀, hin, f2, hout⟩ := ih m₂ v m' h
        exact ⟨k + 1, v₀, m₀, by rw [Interp.run, hev]; exact hin, f2, hout⟩
      | done w m₂ =>
        -- impossible: `.done` is only ever `applyKont`'s empty-continuation arm, so the
        -- control word would have to be a value rather than an expression
        have h1 := (RubyCore.Proof.done_inv m w m₂ hev).1
        rw [hc] at h1
        exact absurd h1 (by simp)
      | uncaught exc m₂ => rw [hev] at h; simp only [RubyCore.Proof.frameR] at h
      | unsupported r => rw [hev] at h; simp only [RubyCore.Proof.frameR] at h
      | stuck r => rw [hev] at h; simp only [RubyCore.Proof.frameR] at h
    | value w =>
      cases hk : m.kont with
      | nil =>
        -- **the pass-through point**: the inner run ends here, in one step
        refine ⟨1, w, m, ?_, n + 1, ?_⟩
        · simp only [Interp.run, Interp.stepFn, hc, Interp.applyKont, hk]
        · rw [← pushK_eq_deliver hc hk, Interp.run]; exact h
      | cons kk rest =>
        have hne : m.kont ≠ [] := by rw [hk]; simp
        have hstep : Interp.stepFn (pushK K m) =
            RubyCore.Proof.frameR K (Interp.stepFn m) := by
          simp only [Interp.stepFn, pushK_eq, RubyCore.Proof.pushK_ctl, hc,
            RubyCore.Proof.applyKont_frame K hK m w hne]
        rw [hstep] at h
        cases hev : Interp.stepFn m with
        | next m₂ =>
          rw [hev] at h
          simp only [RubyCore.Proof.frameR] at h
          obtain ⟨k, v₀, m₀, hin, f2, hout⟩ := ih m₂ v m' h
          exact ⟨k + 1, v₀, m₀, by rw [Interp.run, hev]; exact hin, f2, hout⟩
        | done w₂ m₂ =>
          exact absurd (RubyCore.Proof.done_inv m w₂ m₂ hev).2.1 hne
        | uncaught exc m₂ => rw [hev] at h; simp only [RubyCore.Proof.frameR] at h
        | unsupported r => rw [hev] at h; simp only [RubyCore.Proof.frameR] at h
        | stuck r => rw [hev] at h; simp only [RubyCore.Proof.frameR] at h
    | jump j =>
      cases hk : m.kont with
      | nil =>
        -- the inner run has escaped, and `JumpOpaque` is exactly the statement that the outer
        -- one cannot turn that back into a value
        refine absurd h0 (hJ m j (n + 1) v m' ?_)
        have heq : ({ m with ctl := .jump j, kont := K } : Machine) = pushK K m := by
          rw [pushK, hk, List.nil_append, ← hc]
        rw [heq]
      | cons kk rest =>
        have hne : m.kont ≠ [] := by rw [hk]; simp
        have hstep : Interp.stepFn (pushK K m) =
            RubyCore.Proof.frameR K (Interp.stepFn m) := by
          simp only [Interp.stepFn, pushK_eq, RubyCore.Proof.pushK_ctl, hc,
            RubyCore.Proof.unwind_frame K hK m j hne]
        rw [hstep] at h
        cases hev : Interp.stepFn m with
        | next m₂ =>
          rw [hev] at h
          simp only [RubyCore.Proof.frameR] at h
          obtain ⟨k, v₀, m₀, hin, f2, hout⟩ := ih m₂ v m' h
          exact ⟨k + 1, v₀, m₀, by rw [Interp.run, hev]; exact hin, f2, hout⟩
        | done w₂ m₂ =>
          exact absurd (RubyCore.Proof.done_inv m w₂ m₂ hev).2.1 hne
        | uncaught exc m₂ => rw [hev] at h; simp only [RubyCore.Proof.frameR] at h
        | unsupported r => rw [hev] at h; simp only [RubyCore.Proof.frameR] at h
        | stuck r => rw [hev] at h; simp only [RubyCore.Proof.frameR] at h

end Ratchet.Denote
