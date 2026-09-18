import Denote.Rules.Bounded.BoundedCall

/-! Primitive dispatch already has an unbounded proof. Only receiver/argument composition
needs a bounded counterpart when an operand contains a scoped recursive call. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private theorem recv_one {N : Nat} {κ κ' : Ctx} {I I' : Ty} {site : SendSite} {Γ Γ' : Env}
    {m : Machine} {recv : Value}
    {e : Ratchet.Expr} {σ α τ : Ty} {name : String}
    (hp : DPrim σ name [α] τ) (he : SemSafeCtxAt N κ Γ I e α κ' Γ' I')
    (hplain : plainArgB e = true) (hm : StateOk κ Γ I m) (hr : denM σ m recv)
    (hfree : nameFreeN κ' name = true)
    (hstring : σ = .cls "String" →
      isANoOk κ'.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    RunSpecAt N m (deliverA (.val recv) m [.recvK name [toRuby e] .none site]) Γ' τ κ' I' := by
  apply RunSpecAt.stepWithin (by rfl) (recv_one_step m recv name e hplain)
  apply (he m hm).bindSpec (prim_catchFree _ (by intro tag; simp))
  intro a n hn
  cases a with
  | val v =>
    have hrecv := primitive_framed hp hn.1 hr
    have h := primitive_frame hp (StateOk_deliverA (hn.2.2 v rfl)) rfl
      (m := deliverA (.val v) n []) (denM_deliverA.mpr hrecv)
      (.cons (denM_deliverA.mpr hn.2.1) .nil)
      (start := deliverA (.val v) n [.argsK recv site name [] [] .none])
      (by rfl) (by rfl) hfree hstring
    exact (h.at N).rebase (hn.1.trans (Framed_reCtl _ _ _))
  | esc j =>
    apply RunSpecAt.stepWithin (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpecAt.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩

private theorem recv_spec {N : Nat} {κ κ' : Ctx} {I I' : Ty} {site : SendSite} {Γ Γ' : Env}
    {m : Machine} {recv : Value}
    {es : List Ratchet.Expr} {σ τ : Ty} {tys : List Ty} {name : String}
    (hp : DPrim σ name tys τ) (ha : SemAllCtxAt N κ Γ I es tys κ' Γ' I')
    (hm : StateOk κ Γ I m) (hr : denM σ m recv)
    (hfree : nameFreeN κ' name = true)
    (hstring : σ = .cls "String" →
      isANoOk κ'.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    RunSpecAt N m (deliverA (.val recv) m [.recvK name (toRubyList es) .none site]) Γ' τ κ' I' := by
  have harity : tys = [] ∨ ∃ α, tys = [α] := by
    cases hp <;> simp
  rcases harity with hnil | ⟨α, hone⟩
  · subst hnil
    cases ha
    have h := primitive_frame hp (StateOk_deliverA hm) rfl
      (m := deliverA (.val recv) m []) (denM_deliverA.mpr hr) .nil
      (start := deliverA (.val recv) m [.recvK name [] .none site]) (by rfl) (by rfl) hfree hstring
    exact (h.at N).rebase (Framed_reCtl _ _ _)
  · subst hone
    cases ha with
    | cons he ht hplain =>
      cases ht
      exact recv_one hp he hplain hm hr hfree hstring

theorem SemSafeCtxAt.prim {N : Nat} {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty}
    {recv : Ratchet.Expr} {name : String}
    {args : List Ratchet.Expr} {σ τ : Ty} {tys : List Ty}
    (hr : SemSafeCtxAt N κ Γ I recv σ κ₁ Γ₁ I₁)
    (ha : SemAllCtxAt N κ₁ Γ₁ I₁ args tys κ₂ Γ₂ I₂) (hp : DPrim σ name tys τ)
    (hfree : nameFreeN κ₂ name = true)
    (hstring : σ = .cls "String" →
      isANoOk κ₂.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    SemSafeCtxAt N κ Γ I (.send (some recv) name args none) τ κ₂ Γ₂ I₂ := by
  intro m hm
  let site : SendSite := match toRuby recv with | .self' => .selfRecv | _ => .explicit
  apply RunSpecAt.stepWithin (by rfl)
    (show Interp.stepFn _ =
      .next (pushK [.recvK name (toRubyList args) .none site] (evalFrom m recv)) from ?_)
  · apply (hr m hm).bindSpec (prim_catchFree _ (by intro tag; simp))
    intro a n hn
    cases a with
    | val v => exact (recv_spec hp ha (hn.2.2 v rfl) hn.2.1 hfree hstring).rebase hn.1
    | esc j =>
      apply RunSpecAt.stepWithin (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
      exact RunSpecAt.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩
  · rfl

#print axioms SemSafeCtxAt.prim
end Ratchet.Denote.Typed
