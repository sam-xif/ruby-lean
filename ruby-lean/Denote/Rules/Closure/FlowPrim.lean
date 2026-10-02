import Denote.Judgment.LocalFlow
import Denote.Rules.Primitive.Primitive

/-! A primitive on a flow-typed receiver. The receiver's local facts are consumed by
the bind; the result keeps only the incoming facts' bound slots (as for embed). -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemFlow.prim {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
    {facts out : LocalFacts} {current : Bool} {recv : Ratchet.Expr} {name : String}
    {args : List Ratchet.Expr} {tys : List Ty}
    (hr : SemFlow κ Γ I facts recv σ current κ₁ Γ₁ I₁ out)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args tys κ₂ Γ₂ I₂) (hp : DPrim σ name tys τ)
    (hfree : nameFreeN κ₂ name = true)
    (hstring : σ = .cls "String" →
      isANoOk κ₂.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    SemFlow κ Γ I facts (.send (some recv) name args none) τ false κ₂ Γ₂ I₂ facts.afterEffect := by
  intro m hm hf
  apply RunSpec.withPost ?_
    (fun _ _ hn => ⟨hf.afterEffect hm.frameInRange.2 hn.1, by intro h; cases h⟩)
  let site : SendSite := match toRuby recv with | .self' => .selfRecv | _ => .explicit
  apply RunSpec.step (by rfl)
    (show Interp.stepFn _ =
      .next (pushK [.recvK name (toRubyList args) .none site] (evalFrom m recv)) from ?_)
  · apply (hr m hm hf).erase.bindSpec hm.rootClean (prim_catchFree _ rfl)
    intro a n hn
    cases a with
    | val v => exact (prim_recv_spec hp ha (hn.2.2 v rfl) hn.2.1 hfree hstring).rebase hn.1
    | esc j =>
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
      exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩
  · rfl

#print axioms SemFlow.prim
end Ratchet.Denote.Typed
