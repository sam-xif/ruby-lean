import Denote.Rules.Method.Flow

/-! Calling any expression proved to return the checked callback. Its receiver is
saved before the argument, and callback return preserves all outgoing method aliases. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private theorem recv_one {κ : Ctx} {Γ Γm Γm' : Env} {I σ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Ratchet.Frame} {origin m : Machine}
    {recv : Value} {name param : String} {arg : Ratchet.Expr} {site : SendSite}
    {facts out : CallbackFacts} {callback : Bool}
    (hm : MethodActivation cb fr Γm origin m) (hf : CallbackFactsOk facts m)
    (hr : MethodCallbackReceiver m recv)
    (he : SemMethodFlow cb fr Γm facts arg σ callback Γm' out) (hp : cb.params = [(param, σ)])
    (ht : activationReturnB Γm' = true) (hplain : plainArgB arg = true)
    (hfree : nameFreeN κ name = true) (hname : procCallNameB name = true) :
    MethodRunWith m (deliverA (.val recv) m [.recvK name [toRuby arg] .none site])
      Γ Γm' cb.ret κ (callbackMethodCtx κ fr cb.code) I I (CallbackPost out false) := by
  apply MethodRunWith.step (by rfl) (recv_one_step m recv name arg hplain)
  apply (he origin m hm hf).bind (prim_catchFree _ (by intro tag; simp))
  intro a n hn
  cases a with
  | val v =>
    have active := hm.after hn.1
    have saved := hr.after hm hn.1.1
    have h := callback_invokeWith (m := deliverA (.val v) n [])
      (active.reCtl (.value v) []) ⟨saved.block, saved.klass⟩ hp
      (denM_deliverA.mpr hn.1.2.1) ht hfree hname rfl
      (start := deliverA (.val v) n [.argsK recv site name [] [] .none]) (by rfl) (by rfl)
    have post := (h.mapPost (Q := CallbackPost out false) (fun _ _ _ hcb =>
      ⟨((hn.2 v rfl).1.reCtl (.value v) []).callback (active.reCtl (.value v) []) hcb,
        by intro h; cases h⟩))
    exact post.rebase (hn.1.1.trans (.ordinary (Framed_reCtl _ _ _)))
  | esc j =>
    apply MethodRunWith.step (next := deliverA (.esc j) n []) (by rfl) (by cases j <;> rfl)
    exact MethodRunWith.answer (fun _ _ c k h => h.reCtl c k)
      ⟨⟨hn.1.1, hn.1.2.1, fun _ hv => by cases hv⟩, fun _ hv => by cases hv⟩

/-- Sorbet 0.6.13405 accepts `copy=b; b=nil; copy.call(5)` and repeated calls (clink 241).
The receiver expression must prove actual callback identity; its type alone is insufficient. -/
theorem SemMethodFlow.call {κ : Ctx} {Γ Γm Γm' Γm'' : Env} {I σ τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Ratchet.Frame} {recv arg : Ratchet.Expr}
    {name param : String} {facts mid out : CallbackFacts} {callback : Bool}
    (hr : SemMethodFlow cb fr Γm facts recv τ true Γm' mid)
    (ha : SemMethodFlow cb fr Γm' mid arg σ callback Γm'' out)
    (hp : cb.params = [(param, σ)]) (ht : activationReturnB Γm'' = true)
    (hplain : plainArgB arg = true) (hfree : nameFreeN κ name = true)
    (hname : procCallNameB name = true) :
    SemMethodFlow cb fr Γm facts (.send (some recv) name [arg] none) cb.ret false Γm'' out := by
  intro origin m hm hf
  let site : SendSite := match toRuby recv with | .self' => .selfRecv | _ => .explicit
  apply MethodRunWith.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.recvK name [toRuby arg] .none site] (evalFrom m recv)) from rfl)
  apply (hr origin m hm hf).bind (prim_catchFree _ (by intro tag; simp))
  intro a n hn
  cases a with
  | val v =>
    exact (recv_one (hm.after hn.1) (hn.2 v rfl).1 ((hn.2 v rfl).2 rfl)
      ha hp ht hplain hfree hname).rebase hn.1.1
  | esc j =>
    apply MethodRunWith.step (next := deliverA (.esc j) n []) (by rfl) (by cases j <;> rfl)
    exact MethodRunWith.answer (fun _ _ c k h => h.reCtl c k)
      ⟨⟨hn.1.1, hn.1.2.1, fun _ hv => by cases hv⟩, fun _ hv => by cases hv⟩

#print axioms SemMethodFlow.call
end Ratchet.Denote.Typed
