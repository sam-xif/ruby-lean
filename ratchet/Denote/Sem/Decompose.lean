import Denote.Sem.Frame
import RubyCore.Proof.KontFrameStep
import RubyCore.Proof.NotDone

/-!
# `Denote/Sem/Decompose.lean` — the fifth stall point, cleared

`Denote/Sem/Frame.lean` states the interpreter's frame rule (`KontFrameCatchFree`) and the
decomposition the compound rungs need (`EvalsDecompose`), and states them as *unproved
propositions* — with a refutation of the naive version and a measurement of the corrected
one's cost. This file consumes the proofs, which live where that file said they belong:
`RubyCore/Proof/KontFrame*.lean`, next to `stepFn`.

> **Generalised 2026-09-11.** `Denote/Sem/AnswerValue.lean`'s `run_split_A` is `run_split`
> with the same statement and the same two hypotheses, derived in 41 lines with **no
> induction** from `Denote/Sem/Answer.lean`'s `run_pushK` — which is this induction with the
> four non-`.value` outcomes kept instead of excluded. `JumpOpaque` survives as a hypothesis
> and is spent in one `exact`, in the branch named `esc`. Nothing here is retired; the 48
> discharged rungs consume this file unchanged.

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

/-- `raiseErr` sets the control word to a raise-jump and **leaves the continuation alone** —
which is why a `retJ` or an uncaught `throw` at an empty continuation is still a jump at an
empty continuation one step later. -/
theorem raiseErr_ctl (m : Machine) (cls : ObjId) (msg : String) :
    (Interp.raiseErr m cls msg).ctl =
      .jump (.raiseJ (Builtins.allocExc m cls msg).1) := rfl

theorem raiseErr_kont (m : Machine) (cls : ObjId) (msg : String) :
    (Interp.raiseErr m cls msg).kont = m.kont := rfl

/-- A machine whose control word is a jump and whose continuation is empty never returns a
value, at any fuel. The `retJ` and `throwJ` arms are why this is an induction rather than a
computation: both *step*, to a `raiseErr` — and `raiseErr` leaves the continuation alone, so
the next state is of the same shape.

The jump is **existentially quantified** rather than a parameter, and that is not cosmetic:
with it as a parameter the induction hypothesis cannot be applied at the `retJ` arm, because
the jump the successor state carries is the freshly allocated exception and Lean has nothing to
synthesise it from until the `.ctl` premise is elaborated. -/
theorem jump_empty_never_value :
    ∀ (fuel : Nat) (m : Machine) (v : Value) (m' : Machine),
      (∃ j, m.ctl = .jump j) → m.kont = [] → Interp.run fuel m ≠ .value v m' := by
  intro fuel
  induction fuel with
  | zero => intro m v m' _ _ h; exact absurd h (by simp [Interp.run])
  | succ n ih =>
    intro m v m' hc hk h
    obtain ⟨j, hc⟩ := hc
    -- `simp only` for the `stepFn` match (a `rw` leaves `match Ctl.jump j with …` standing),
    -- then the two rewrites that expose `unwind`'s empty-continuation arm
    simp only [Interp.run, Interp.stepFn, hc] at h
    rw [Interp.unwind.eq_def, hk] at h
    -- All three scrutinees are constructor applications once `j` is one, and **none of the
    -- three matches reduces on its own** — they are matcher applications, so `h` reads
    -- `match (match [] with | [] => match Jump.throwJ … ) with …` until `dsimp` runs.
    cases j
    all_goals (try (dsimp only at h))
    case raiseJ exc => exact absurd h (by simp)
    case retJ w target =>
      exact ih _ v m' ⟨_, raiseErr_ctl m _ _⟩ (by rw [raiseErr_kont, hk]) h
    case throwJ tag w =>
      -- the inner match: `split at h` would peel `run`'s five-arm one instead
      cases hins : Builtins.inspectP m tag with
      | error e => rw [hins] at h; dsimp only at h; exact absurd h (by simp)
      | ok r =>
        rw [hins] at h
        dsimp only at h
        exact ih _ v m' ⟨_, raiseErr_ctl m _ _⟩ (by rw [raiseErr_kont, hk]) h
    case brkJ w => exact absurd h (by simp)
    case nxtJ w => exact absurd h (by simp)
    case redoJ => exact absurd h (by simp)
    case retryJ => exact absurd h (by simp)

/-- `[.asgnK kind x]` is jump-opaque: `unwind`'s default arm passes the jump straight through
with the frame popped, which lands on `jump_empty_never_value`. This is the continuation
`Judge.vasgn` pushes, and the shape every other rule's literal kont will follow. -/
theorem jumpOpaque_asgnK (kind : RubyCore.VarKind) (x : String) :
    JumpOpaque [.asgnK kind x] := by
  intro m j fuel v m' h
  match fuel with
  | 0 => exact absurd h (by simp [Interp.run])
  | f + 1 =>
    rw [Interp.run] at h
    have hs : Interp.stepFn { m with ctl := .jump j, kont := [.asgnK kind x] }
        = .next (Interp.withCtl { m with ctl := .jump j, kont := [] } (.jump j)) := rfl
    rw [hs] at h
    exact jump_empty_never_value f _ v m' ⟨j, rfl⟩ rfl h

/-! ## The decomposition -/

/-- The delivery state: the machine a sub-run ends at, seen from outside — its own value in
flight, and the outer continuation still to go. -/
abbrev deliver (m : Machine) (v : Value) (K : List Kont) : Machine :=
  { m with ctl := .value v, kont := K }

/-- At an empty continuation with a value in flight, `pushK K` *is* the delivery state. This
is the pass-through point, and it is a `rfl`. -/
theorem pushK_eq_deliver (K : List Kont) {m : Machine} {w : Value} (hc : m.ctl = .value w)
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
        Interp.run n m = .value v₀ m₀ ∧ m₀.ctl = .value v₀ ∧ m₀.kont = [] ∧
        ∃ f2, Interp.run f2 (deliver m₀ v₀ K) = .value v m' := by
  intro fuel
  induction fuel with
  | zero => intro m v m' h; exact absurd h (by simp [Interp.run])
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
        obtain ⟨k, v₀, m₀, hin, hc₀, hk₀, f2, hout⟩ := ih m₂ v m' h
        exact ⟨k + 1, v₀, m₀, by rw [Interp.run, hev]; exact hin, hc₀, hk₀, f2, hout⟩
      | done w m₂ =>
        -- impossible: `.done` is only ever `applyKont`'s empty-continuation arm, so the
        -- control word would have to be a value rather than an expression
        have h1 := (RubyCore.Proof.done_inv m w m₂ hev).1
        rw [hc] at h1
        exact absurd h1 (by simp)
      | uncaught exc m₂ => rw [hev] at h; exact absurd h (by simp [RubyCore.Proof.frameR])
      | unsupported r => rw [hev] at h; exact absurd h (by simp [RubyCore.Proof.frameR])
      | stuck r => rw [hev] at h; exact absurd h (by simp [RubyCore.Proof.frameR])
    | value w =>
      cases hk : m.kont with
      | nil =>
        -- **the pass-through point**: the inner run ends here, in one step
        refine ⟨1, w, m, ?_, hc, hk, n + 1, ?_⟩
        · simp only [Interp.run, Interp.stepFn, hc, Interp.applyKont, hk]
        · rw [← pushK_eq_deliver K hc hk, Interp.run]; exact h
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
        | uncaught exc m₂ => rw [hev] at h; exact absurd h (by simp [RubyCore.Proof.frameR])
        | unsupported r => rw [hev] at h; exact absurd h (by simp [RubyCore.Proof.frameR])
        | stuck r => rw [hev] at h; exact absurd h (by simp [RubyCore.Proof.frameR])
    | jump j =>
      cases hk : m.kont with
      | nil =>
        -- the inner run has escaped, and `JumpOpaque` is exactly the statement that the outer
        -- one cannot turn that back into a value
        exfalso
        have heq : ({ m with ctl := .jump j, kont := K } : Machine) = pushK K m := by
          rw [pushK, hk, List.nil_append, ← hc]
        exact hJ m j (n + 1) v m' (by rw [heq]; exact h0)
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
        | uncaught exc m₂ => rw [hev] at h; exact absurd h (by simp [RubyCore.Proof.frameR])
        | unsupported r => rw [hev] at h; exact absurd h (by simp [RubyCore.Proof.frameR])
        | stuck r => rw [hev] at h; exact absurd h (by simp [RubyCore.Proof.frameR])

end Ratchet.Denote
