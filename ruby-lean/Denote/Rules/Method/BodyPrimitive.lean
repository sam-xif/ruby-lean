import Denote.Rules.Method.BodyLists
import Denote.Rules.Primitive.Primitive

/-! Primitive sends inside a callback-capable method. Receiver evaluation precedes
argument evaluation; saved receiver types survive their mixed effects. Native dispatch
reuses the existing primitive proof with full active-method and caller conformance. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private theorem primitive_receiver {σ τ : Ty} {name : String} {tys : List Ty}
    (hp : DPrim σ name tys τ) {m n : Machine} {v : Value}
    (h : MethodEffects m n) (hv : denM σ m v) : denM σ n v := by
  apply h.firstOrder (τ := σ) ?_ hv
  cases hp with
  | arrayIndex hfo => exact hfo
  | hashIndex hfo => exact hfo
  | _ => rfl

private theorem recv_one {κ : Ctx} {Γ Γm Γm' : Env} {I σ α τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Ratchet.Frame} {e : Ratchet.Expr} {name : String}
    {origin m : Machine} {recv : Value} {site : SendSite}
    (hp : DPrim σ name [α] τ) (he : SemMethod cb fr Γm e α Γm')
    (hplain : plainArgB e = true) (hm : MethodActivation cb fr Γm origin m) (hr : denM σ m recv)
    (hfree : nameFreeN κ name = true)
    (hstring : σ = .cls "String" → isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    MethodRunSpec m (deliverA (.val recv) m [.recvK name [toRuby e] .none site])
      Γ Γm' τ κ (callbackMethodCtx κ fr cb.code) I I := by
  apply MethodRunSpec.step (by rfl) (recv_one_step m recv name e hplain)
  apply (he origin m hm).bind (prim_catchFree _ (by intro tag; simp))
  intro a n hn
  cases a with
  | val v =>
    have hrecv := primitive_receiver hp hn.1 hr
    have active := hm.after hn
    have h := primitive_frame hp (StateOk_deliverA active.method) rfl
      (m := deliverA (.val v) n []) (denM_deliverA.mpr hrecv)
      (.cons (denM_deliverA.mpr hn.2.1) .nil)
      (start := deliverA (.val v) n [.argsK recv site name [] [] .none])
      (by rfl) (by rfl) hfree hstring
    exact (h.inMethod (active.reCtl (.value v) [])).rebase
      (hn.1.trans (.ordinary (Framed_reCtl _ _ _)))
  | esc j =>
    apply MethodRunSpec.step (next := deliverA (.esc j) n []) (by rfl) (by cases j <;> rfl)
    apply MethodRunSpec.answer (a := .esc j) (n := n)
    exact ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩

private theorem recv_spec {κ : Ctx} {Γ Γm Γm' : Env} {I σ τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Ratchet.Frame} {es : List Ratchet.Expr} {tys : List Ty}
    {name : String} {origin m : Machine} {recv : Value} {site : SendSite}
    (hp : DPrim σ name tys τ) (ha : SemMethodAll cb fr Γm es tys Γm')
    (hm : MethodActivation cb fr Γm origin m) (hr : denM σ m recv)
    (hfree : nameFreeN κ name = true)
    (hstring : σ = .cls "String" → isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    MethodRunSpec m (deliverA (.val recv) m [.recvK name (toRubyList es) .none site])
      Γ Γm' τ κ (callbackMethodCtx κ fr cb.code) I I := by
  have harity : tys = [] ∨ ∃ α, tys = [α] := by cases hp <;> simp
  rcases harity with hnil | ⟨α, hone⟩
  · subst hnil
    cases ha
    have h := primitive_frame hp (StateOk_deliverA hm.method) rfl
      (m := deliverA (.val recv) m []) (denM_deliverA.mpr hr) .nil
      (start := deliverA (.val recv) m [.recvK name [] .none site]) (by rfl) (by rfl) hfree hstring
    exact (h.inMethod (hm.reCtl (.value recv) [])).rebase (.ordinary (Framed_reCtl _ _ _))
  · subst hone
    cases ha with
    | cons he ht hplain =>
      cases ht
      exact recv_one hp he hplain hm hr hfree hstring

/-- Use all existing primitive rows with callback-capable operands. Sorbet 0.6.13405
accepts Integer `yield(1) + yield(2)` under a typed Proc parameter and rejects a String
right operand (clink 235). Dispatch guards and exact argument types remain mandatory. -/
theorem SemMethod.prim {κ : Ctx} {Γ Γm Γm' Γm'' : Env} {I σ τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Ratchet.Frame} {recv : Ratchet.Expr} {name : String}
    {args : List Ratchet.Expr} {tys : List Ty}
    (hr : SemMethod cb fr Γm recv σ Γm') (ha : SemMethodAll cb fr Γm' args tys Γm'')
    (hp : DPrim σ name tys τ) (hfree : nameFreeN κ name = true)
    (hstring : σ = .cls "String" → isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    SemMethod cb fr Γm (.send (some recv) name args none) τ Γm'' := by
  intro origin m hm
  let site : SendSite := match toRuby recv with | .self' => .selfRecv | _ => .explicit
  apply MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.recvK name (toRubyList args) .none site] (evalFrom m recv)) from rfl)
  apply (hr origin m hm).bind (prim_catchFree _ (by intro tag; simp))
  intro a n hn
  cases a with
  | val v => exact (recv_spec hp ha (hm.after hn) hn.2.1 hfree hstring).rebase hn.1
  | esc j =>
    apply MethodRunSpec.step (next := deliverA (.esc j) n []) (by rfl) (by cases j <;> rfl)
    apply MethodRunSpec.answer (a := .esc j) (n := n)
    exact ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩

#print axioms SemMethod.prim
end Ratchet.Denote.Typed
