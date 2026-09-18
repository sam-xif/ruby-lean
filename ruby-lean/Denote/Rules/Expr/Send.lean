import Denote.Rules.Method.MethodArgs

/-! Receiver-first sends with arbitrary argument lists. The receiver's first-order type
survives every argument, and the dispatch contract consumes the final context and values. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.sendVia {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
    {recv : Ratchet.Expr} {name : String} {args : List Ratchet.Expr} {tys : List Ty}
    {site : SendSite}
    (hr : SemSafeCtxA κ Γ I recv σ κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args tys κ₂ Γ₂ I₂)
    (hsite : (match toRuby recv with | .self' => .selfRecv | _ => .explicit) = site)
    (hσ : FirstOrder σ = true) (ht : ∀ t ∈ tys, FirstOrder t = true)
    (finish : ∀ m, StateOk κ₂ Γ₂ I₂ m → m.kont = [] → ∀ v, denM σ m v →
      ∀ vs, DenAll tys m vs → StepSpec m Γ₂ τ (Interp.finishSend m v site name vs .none) κ₂ I₂) :
    SemSafeCtxA κ Γ I (.send (some recv) name args none) τ κ₂ Γ₂ I₂ := by
  intro m hm
  apply RunSpec.step (by rfl)
    (show Interp.stepFn _ =
      .next (pushK [.recvK name (toRubyList args) .none site] (evalFrom m recv)) from ?_)
  · apply (hr m hm).bindSpec (prim_catchFree _ (by intro tag; simp))
    intro a n hn
    cases a with
    | val v =>
      have hfr : Framed n (deliverA (.val v) n []) := Framed_reCtl _ _ _
      have hs := ha.startArgsKeep (site := site) (P := fun n => denM σ n v)
        (m := deliverA (.val v) n [])
        (name := name) (recv := v) (StateOk_deliverA (hn.2.2 v rfl)) rfl [] []
        (by simpa using ht) trivial (fun hf hv => hf.firstOrder σ hσ v hv)
        (denM_deliverA.mpr hn.2.1) (fun n hn hk hv => finish n hn hk v hv)
      have hb : RunSpec (deliverA (.val v) n [])
          (deliverA (.val v) n [.recvK name (toRubyList args) .none site]) Γ₂ τ κ₂ I₂ := by
        apply RunSpec.of_stepSpec (by rfl)
        exact hs
      exact hb.rebase (hn.1.trans hfr)
    | esc j =>
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
      exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩
  · rw [← hsite]; rfl

#print axioms SemSafeCtxA.sendVia
end Ratchet.Denote.Typed
