import Denote.Sem.Send
import Denote.Sem.Obligations
import Denote.Join

/-!
# `Denote/Rules/Never.lean` — the rules that conclude `Ty.never`

`Ty.never` is the empty type: `denM .never m v` is `False` for every value. So a rule whose
conclusion type is `never` is saying **the expression does not return**, and its obligation is
discharged by contradicting the run rather than by typing a value.

`Judge.callNever` is the first of the call family, and it is the one that needs least: the
argument walk (`../Sem/Send.lean`'s `run_args`) plus the fact that an argument typed `never`
cannot have produced the value the walk found.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## `denM .never` is empty -/

theorem denM_never {m : Machine} {v : Value} : ¬ denM .never m v := by
  simp [denM]

/-- An argument list cannot deliver values if one of its types is `never`. This is `DenAllAt`
read backwards, and the induction is on the list because that is where the pairing lives. -/
theorem not_denAllAt_of_never :
    ∀ (es : List Ratchet.Expr) (τs : List Ty) (vs : List Value) (m m' : Machine),
      τs.contains Ty.never = true → ¬ DenAllAt m es τs vs m' := by
  intro es
  induction es with
  | nil =>
    intro τs vs m m' hc h
    cases τs with
    | nil => exact absurd hc (by simp)
    | cons τ τs => cases vs <;> exact absurd h (by simp [DenAllAt])
  | cons e es ih =>
    intro τs vs m m' hc h
    cases τs with
    | nil => exact absurd hc (by simp)
    | cons τ τs =>
      cases vs with
      | nil => exact absurd h (by simp [DenAllAt])
      | cons v vs =>
        obtain ⟨m₁, _, hden, hrest⟩ := h
        -- `Ty` has no `LawfulBEq` instance, so the membership is taken apart with
        -- `Denote/Join.lean`'s `ty_eq_of_beq` rather than with `List.mem_of_elem_eq_true`
        simp only [List.contains_cons, Bool.or_eq_true] at hc
        rcases hc with h' | h'
        · rw [← ty_eq_of_beq h'] at hden; exact denM_never hden
        · exact ih τs vs m₁ m' h' hrest

/-! ## The rung -/

/-- The first step of an implicit-self send: straight into `startArgs`, with no `.recvK`
(there is no receiver to evaluate). `rfl`. -/
theorem stepFn_vcall_send (m : Machine) (mname : String) (args : List Ratchet.Expr) :
    Interp.stepFn (evalFrom m (.send none mname args none))
      = Interp.startArgs (evalFrom m (.send none mname args none))
          (evalFrom m (.send none mname args none)).currentFrame.self .implicit mname []
          (toRubyList args) .none := rfl

theorem Sem.Judge.callNever : Obl.Judge.callNever := by
  intro κ Γ Γ' I I' mname args argTys hall hnever
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  exfalso
  obtain ⟨fuel, hrun⟩ := hev
  -- the run took at least one step, and that step is `startArgs`
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | f + 1 =>
    have hsr : StepRunsTo (Interp.stepFn (evalFrom m (.send none mname args none))) v m' := by
      refine stepRunsTo_of_run ?_ hrun
      -- `stepFn` at an `.eval` is `evalExpr`, which never ends a run
      have he : Interp.stepFn (evalFrom m (.send none mname args none))
          = Interp.evalExpr (evalFrom m (.send none mname args none))
              (toRuby (.send none mname args none)) := rfl
      rw [he]
      exact RubyCore.Proof.evalExpr_notDone
    rw [stepFn_vcall_send] at hsr
    -- the argument walk: each argument returned, at the machine the previous one left
    obtain ⟨vs, m₁, hallEv, _, _⟩ :=
      run_args .implicit mname (evalFrom m (.send none mname args none)).currentFrame.self
        .none args [] (evalFrom m (.send none mname args none)) v m' rfl hall.1 hsr
    -- …and the premise says one of their types is `never`, which no value has
    obtain ⟨_, hden, _⟩ :=
      hall.2 (evalFrom m (.send none mname args none))
        (StateOk_reCtl hm _ _) vs m₁ hallEv
    exact not_denAllAt_of_never args argTys vs _ m₁ hnever hden

/-- The `.recvK` delivery: `applyKont` pops it and starts the argument walk with the receiver's
value in hand. `rfl`. -/
theorem stepFn_recvK (m : Machine) (v : Value) (mname : String)
    (args : List RubyCore.Expr) (pblk : PendingBlk) (site : SendSite) :
    Interp.stepFn (deliver m v [.recvK mname args pblk site])
      = Interp.startArgs { m with ctl := .value v, kont := [] } v site mname [] args pblk := rfl

theorem Sem.Judge.primNever : Obl.Judge.primNever := by
  intro κ Γ Γ₁ Γ₂ I I₁ I₂ recv mname args σ argTys hrecv hargs hnever
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  exfalso
  obtain ⟨fuel, hrun⟩ := hev
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | f + 1 =>
    -- **the receiver link**
    rw [run_succ, stepFn_send_push] at hrun
    -- the matcher `run_succ` leaves does not iota-reduce on its own
    dsimp only at hrun
    obtain ⟨n, v₀, m₀, hin, hc₀, hk₀, f₂, hout⟩ :=
      run_split _ (catchFree_recvK mname (toRubyList args) .none _)
        (jumpOpaque_recvK mname (toRubyList args) .none _) f (evalFrom m recv) v m' hrun
    obtain ⟨_, hdenRecv, hok₁, -⟩ := hrecv.2 m hm v₀ m₀ ⟨n, hin⟩
    rcases hnever with hσ | hargNever
    · -- the receiver's own type is `never`
      subst hσ
      exact denM_never hdenRecv
    · -- **the argument link**, which needs the receiver's delivery stepped through first
      match f₂ with
      | 0 => rw [run_zero] at hout; exact absurd hout (by simp)
      | f₃ + 1 =>
        have hsr : StepRunsTo (Interp.stepFn
            (deliver m₀ v₀ [.recvK mname (toRubyList args) .none
              (match toRuby recv with | .self' => .selfRecv | _ => .explicit)])) v m' := by
          refine stepRunsTo_of_run ?_ hout
          exact RubyCore.Proof.applyKont_notDone
            (deliver m₀ v₀ [.recvK mname (toRubyList args) .none
              (match toRuby recv with | .self' => .selfRecv | _ => .explicit)]) v₀
            (by simp [deliver])
        rw [stepFn_recvK] at hsr
        have hm₀ : ({ m₀ with ctl := .value v₀, kont := [] } : Machine) = m₀ := by
          rw [← hc₀, ← hk₀]
        rw [hm₀] at hsr
        obtain ⟨vs, m₁, hallEv, _, _⟩ :=
          run_args _ mname v₀ .none args [] m₀ v m' hk₀ hargs.1 hsr
        obtain ⟨_, hden, _⟩ := hargs.2 m₀ hok₁ vs m₁ hallEv
        exact not_denAllAt_of_never args argTys vs m₀ m₁ hargNever hden

#print axioms Sem.Judge.callNever
#print axioms Sem.Judge.primNever

end Ratchet.Denote
