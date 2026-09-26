import Denote.Judgment.LocalFlow
import Denote.Rules.Closure.Literal

/-! Source-level creation and assignment carry actual result origins. Slot updates
use the uncaptured main activation; captured-body effects need a different transfer. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemFlow.nilLit {κ : Ctx} {Γ : Env} {I : Ty} (facts : LocalFacts) :
    SemFlow κ Γ I facts .nil .nilT false κ Γ I facts := by
  apply SemFlow.leaf
  intro m hm hf
  exact ⟨m, .nil, rfl, ⟨.refl m, by simp [AnsOk, denM, isNilV], fun _ _ => hm⟩,
    hf, by intro h; cases h⟩

theorem SemFlow.closureLiteral {κ : Ctx} {Γ : Env} {I : Ty} (facts : LocalFacts)
    (code : ClosureCode) (hf : nameFreeN κ (if code.lam then "lambda" else "proc") = true) :
    SemFlow κ Γ I facts (.send none (if code.lam then "lambda" else "proc") []
      (some (.block code.params code.locals code.body)))
      (.clos code (envToSpine Γ) (κ.selfTy.getD .never)) true κ Γ I facts := by
  apply SemFlow.leaf
  intro m hm hfacts
  exact ⟨_, _, closure_literal_step hm code.lam hf code.params code.locals code.body,
    ⟨Framed.of_ext (reified_ext hm _ _ _ _), reified_den hm code,
      fun _ _ => reified_state hm _ _ _ _⟩,
    hfacts.ext (reified_ext hm _ _ _ _), fun _ => currentProc_reified m code⟩

theorem SemFlow.vasgn {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {facts out : LocalFacts}
    {e : Ratchet.Expr} {x : String} {current : Bool}
    (h : SemFlow κ Γ I facts e τ current κ' Γ' I' out)
    (hc : capStale x τ τ = false) (ha : isAliasTy τ = false)
    (hk : capStaleCtx x τ κ' = false) (hmain : κ'.scope.runtimeMain = true) :
    SemFlow κ Γ I facts (.vasgn .lvar x e) τ current κ' (envAfter Γ' x τ)
      (killClosOverSpine I' x τ) (out.write x current) := by
  intro m hm hf
  apply RunWith.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn (evalFrom m (.vasgn .lvar x e)) =
      .next (pushK [.asgnK .lvar x] (evalFrom m e)) from rfl)
  apply (h m hm hf).bind (catchFree_asgnK x)
  intro a n hr
  cases a with
  | val v =>
    let base := reCtl n (.value v) []
    have hn : StateOk κ' Γ' I' base := StateOk_reCtl (hr.1.2.2 v rfl) _ _
    have hd : denM τ base v := denM_reCtl.mpr hr.1.2.1
    have hp : FlowPost out current v base := (hr.2 v rfl).reCtl _ _
    have hout : StateOk κ' (envAfter Γ' x τ) (killClosOverSpine I' x τ)
        (base.setLocal x v) := StateOk_setLocal hn hd hc hk (ρ := τ)
          (by cases τ <;> simp_all [stripAlias, isAliasTy])
          (by intro y σ hy; rw [hy] at ha; simp [isAliasTy] at ha)
    have hlocal := hp.1.write hn.frameInRange.2 (by
      rw [← currentFrame_headD hn.frameInRange.1]; exact (hn.runtime hmain).captured) x v current hp.2
    apply RunWith.step (by rfl)
      (show Interp.stepFn (deliverA (.val v) n [.asgnK .lvar x]) =
        .next (deliverA (.val v) (base.setLocal x v) []) from rfl)
    apply RunWith.answer (fun _ _ c k hp => hp.reCtl c k)
    exact ⟨⟨hr.1.1.trans ((Framed_reCtl n _ []).trans (Framed_setLocal base x v)),
      denM_setLocal hd hc hd, fun _ _ => hout⟩,
      fun _ he => by cases he; exact ⟨hlocal, fun hc => (hp.2 hc).setLocal x v⟩⟩
  | esc j =>
    apply RunWith.step (by rfl)
      (show Interp.stepFn (deliverA (.esc j) n [.asgnK .lvar x]) =
        .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunWith.answer (fun _ _ c k hp => hp.reCtl c k)
      ⟨⟨hr.1.1, hr.1.2.1, fun _ hv => by cases hv⟩, fun _ hv => by cases hv⟩

#print axioms SemFlow.closureLiteral
#print axioms SemFlow.vasgn
end Ratchet.Denote.Typed
