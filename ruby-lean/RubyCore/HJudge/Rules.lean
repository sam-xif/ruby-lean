/-
  RubyCore.HJudge.Rules — the three step-lifting rules, thin wrappers over
  iris-lean's OwnP lifting.

  **Ported from `mdd/sorbet-lean/SorbetLean/Rules.lean`** (spike S1; cerberus
  `RelSem/IrisRules.lean` + `PerStepIris.lean` shapes).

  `ownP_lift_det_step_no_fork` is re-derived here: the library ships the
  atomic-det and pure-det variants only; a machine stepping running→running
  needs the mixed form (deterministic state change, successor an arbitrary
  expression). Statement and proof follow cerberus-lean
  `RelSem/PerStepIris.lean` (their "shaped for upstreaming" note applies —
  if it lands upstream, this section deletes).

  House rules: no sorry, no new axioms.
-/
import Iris.ProgramLogic.OwnP
import RubyCore.HJudge.StateInterp

set_option autoImplicit false

namespace RubyCore.HJudge

open RubyCore
open Iris Iris.ProgramLogic Iris.BI

/-! ## Generic: deterministic non-value step against OwnP (cerberus
    `PerStepIris.lean` §GenericLifting, re-derived) -/

section GenericLifting

variable {Expr State Obs Val : Type _} {GF : BundledGFunctors}
variable [Language Expr State Obs Val] [OwnPGS State GF]
variable {s : Stuckness} {E : CoPset}

theorem ownP_lift_det_step_no_fork {e₁ e₂ : Expr} {σ₁ σ₂ : State}
    {Φ : Val → IProp GF}
    (Hsafe : ReducibleOrNotVal s (e₁, σ₁))
    (Hdet : ∀ {obs' : List Obs} {e₂' : Expr} {σ₂' : State}
        {eₜ' : List Expr},
      PrimStep.primStep (e₁, σ₁) obs' (e₂', σ₂', eₜ') →
      σ₂' = σ₂ ∧ e₂' = e₂ ∧ eₜ' = []) :
    ▷ ownP σ₁ ∗ ▷ (ownP σ₂ -∗ WP e₂ @ s ; E {{ Φ }}) ⊢
      WP e₁ @ s ; E {{ Φ }} := by
  iintro ⟨Hσ₁, Hcont⟩
  iapply ownP_lift_step
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iexists σ₁
  iframe Hσ₁ %Hsafe
  iintro !> %obs %e₂' %σ₂' %eₜ' %Hstep Hσ₂
  obtain ⟨rfl, rfl, rfl⟩ := Hdet Hstep
  imod Hclose
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil]
  iframe
  iapply Hcont $$ Hσ₂

end GenericLifting

/-! ## The RubyCore step rules -/

variable {GF : BundledGFunctors} [RubyGS GF]
variable {s : Stuckness} {E : CoPset}

/-- RETURN: a `done` configuration is a value. -/
theorem wp_done {o : ROutcome} {Φ : ROutcome → IProp GF} :
    Φ o ⊢ WP (RExpr.done o) @ s ; E {{ Φ }} :=
  wp_value'

/-- STEP, running head: one deterministic machine step running → running. -/
theorem wp_step_next {c : MCfg} {h : Heap} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .next m')
    {Φ : ROutcome → IProp GF} :
    ▷ stateIs h ∗ ▷ (stateIs m'.heap -∗ WP (RExpr.running m'.cfg) @ s ; E {{ Φ }}) ⊢
      WP (RExpr.running c) @ s ; E {{ Φ }} := by
  have Hsafe : ReducibleOrNotVal s ((RExpr.running c), h) := by
    cases s
    · exact reducible_of_next hf
    · rfl
  exact ownP_lift_det_step_no_fork Hsafe (fun hstep =>
    let ⟨hσ, he, hefs⟩ := step_next_inv hf hstep
    ⟨hσ, he, hefs⟩)

/-- STEP, terminal value: the machine completes with `v`. -/
theorem wp_step_val {c : MCfg} {h : Heap} {v : Value} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .done v m')
    {Φ : ROutcome → IProp GF} :
    stateIs h ∗ (stateIs m'.heap -∗ Φ (.val v m'.heap)) ⊢
      WP (RExpr.running c) @ s ; E {{ Φ }} := by
  have Hsafe : ReducibleOrNotVal s ((RExpr.running c), h) := by
    cases s
    · exact reducible_of_val hf
    · rfl
  have Hdet : ∀ {obs' : List Empty} {e₂' : RExpr} {σ₂' : Heap}
      {eₜ' : List RExpr},
      PrimStep.primStep ((RExpr.running c), h) obs' (e₂', σ₂', eₜ') →
      σ₂' = m'.heap ∧ ToVal.toVal e₂' = some (ROutcome.val v m'.heap) ∧ eₜ' = [] := by
    intro obs' e₂' σ₂' eₜ' hstep
    obtain ⟨hσ, he, hefs⟩ := step_val_inv hf hstep
    exact ⟨hσ, he ▸ rfl, hefs⟩
  have htriple := ownP_lift_atomic_det_step_no_fork
    (GF := GF) (s := s) (E := E)
    (e₁ := (RExpr.running c)) (σ₁ := h) (σ₂ := m'.heap)
    (v₂ := ROutcome.val v m'.heap) Hsafe Hdet
  iintro ⟨Hst, HΦ⟩
  iapply htriple $$ Hst HΦ

/-- STEP, uncaught exception: the outcome is a VALUE — specs exclude it
    explicitly (never stuckness). -/
theorem wp_step_exc {c : MCfg} {h : Heap} {e : Value} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .uncaught e m')
    {Φ : ROutcome → IProp GF} :
    stateIs h ∗ (stateIs m'.heap -∗ Φ (.exc e m'.heap)) ⊢
      WP (RExpr.running c) @ s ; E {{ Φ }} := by
  have Hsafe : ReducibleOrNotVal s ((RExpr.running c), h) := by
    cases s
    · exact reducible_of_exc hf
    · rfl
  have Hdet : ∀ {obs' : List Empty} {e₂' : RExpr} {σ₂' : Heap}
      {eₜ' : List RExpr},
      PrimStep.primStep ((RExpr.running c), h) obs' (e₂', σ₂', eₜ') →
      σ₂' = m'.heap ∧ ToVal.toVal e₂' = some (ROutcome.exc e m'.heap) ∧ eₜ' = [] := by
    intro obs' e₂' σ₂' eₜ' hstep
    obtain ⟨hσ, he, hefs⟩ := step_exc_inv hf hstep
    exact ⟨hσ, he ▸ rfl, hefs⟩
  have htriple := ownP_lift_atomic_det_step_no_fork
    (GF := GF) (s := s) (E := E)
    (e₁ := (RExpr.running c)) (σ₁ := h) (σ₂ := m'.heap)
    (v₂ := ROutcome.exc e m'.heap) Hsafe Hdet
  iintro ⟨Hst, HΦ⟩
  iapply htriple $$ Hst HΦ

end RubyCore.HJudge
