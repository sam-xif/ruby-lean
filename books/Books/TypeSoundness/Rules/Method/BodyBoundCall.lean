import Books.TypeSoundness.Rules.Method.BodyContext
import Books.TypeSoundness.Rules.Closure.Call
import Books.TypeSoundness.Rules.Primitive.Primitive

/-! Calling the actual callback through a saved receiver. A code-only closure type
does not identify its capture or guarantee native Proc dispatch. These facts belong
to the receiver before argument evaluation, which may overwrite its source local. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

structure MethodCallbackReceiver (m : Machine) (v : Value) : Prop where
  block : m.currentFrame.blk = some v
  klass : classOf m.heap v = Boot.procId

theorem MethodCallbackReceiver.after {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m n : Machine} {v : Value}
    (hr : MethodCallbackReceiver m v) (hm : MethodActivation cb fr Γm origin m)
    (h : MethodEffects m n) : MethodCallbackReceiver n v := by
  obtain ⟨o, cl, hb, hp, _, _⟩ := hm.callback
  have hv : v = .ref o := Option.some.inj (hr.block.symm.trans hb)
  subst v
  exact ⟨(congrArg FrameScope.blk (h.scope hm.method.frameInRange)).trans hr.block,
    (h.procs.dispatch (.ref o) cl (by simp only [procClosure?, hp])).trans hr.klass⟩

theorem callback_invokeWith {κ : Ctx} {Γ Γm : Env} {I σ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m start : Machine}
    {recv v : Value} {name param : String} {site : SendSite}
    (hm : MethodActivation cb fr Γm origin m) (hr : MethodCallbackReceiver m recv)
    (hp : cb.params = [(param, σ)]) (hv : denM σ m v)
    (ht : activationReturnB Γm = true) (hfree : nameFreeN κ name = true)
    (hname : procCallNameB name = true) (hk : m.kont = [])
    (hap : answerPoint start = none)
    (hs : Interp.stepFn start = Interp.invoke m recv site name [v] none []) :
    MethodRunWith m start Γ Γm cb.ret κ (callbackMethodCtx κ fr cb.code) I I
      (fun _ n => CallbackFramed m n) := by
  obtain ⟨o, cl, hblk, hproc, hcode, hc⟩ := hm.callback
  have hrecv : recv = .ref o := Option.some.inj (hr.block.symm.trans hblk)
  have hpay : procClosure? m.heap recv = some cl := by
    simp only [hrecv, procClosure?, hproc]
  have hσ : activationStableB σ = true := by
    have hi := cb.inputTypes
    rw [hp] at hi
    have first := List.all_eq_true.mp hi (param, σ) (by simp)
    simp only [Bool.and_eq_true] at first
    exact first.1
  have hparams : cl.params = (cb.params.map (·.1)).map RubyCore.Param.req :=
    hcode.1.trans (by rw [cb.required]; exact toRubyParams_required cb.params)
  have hlen : [v].length = cb.params.length := by rw [hp]; rfl
  have hargs : DenAll (cb.params.map (·.2)) (popMethodFrame m) [v] := by
    rw [hp]
    exact ⟨activationStable_heap (m := m) hσ rfl hv, trivial⟩
  rw [invoke_proc_dispatch hpay (hm.method.procDispatch hfree hname) hname hr.klass [v] site] at hs
  rw [callClosure_required m cl (cb.params.map (·.1)) [v] _ none none hparams
    (by simpa only [List.length_map] using hlen) hcode.2.2.2.2.1 hcode.2.2.2.2.2, hcode.2.2.1] at hs
  apply MethodRunWith.step hap (by
    simpa only [Interp.withKont, pushMethodFrame, hk] using hs)
  exact checked_callback_method_runWith hc hm.method hm.scope hm.distinct hlen hargs
      cb.main cb.returnFO (by simpa only [hcode.2.1] using cb.inputTypes) cb.outputTypes ht
      (by simpa only [hcode.2.1] using cb.fixed) (by simpa only [hcode.2.1] using cb.body)

theorem saved_callback_call_run {κ : Ctx} {Γ Γm Γm' : Env} {I σ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m : Machine}
    {recv : Value} {name param : String} {arg : Checker.Expr} {site : SendSite}
    (hm : MethodActivation cb fr Γm origin m) (hr : MethodCallbackReceiver m recv)
    (he : SemMethod cb fr Γm arg σ Γm') (hp : cb.params = [(param, σ)])
    (ht : activationReturnB Γm' = true) (hplain : plainArgB arg = true)
    (hfree : nameFreeN κ name = true) (hname : procCallNameB name = true) :
    MethodRunSpec m (deliverA (.val recv) m [.recvK name [toRuby arg] .none site])
      Γ Γm' cb.ret κ (callbackMethodCtx κ fr cb.code) I I := by
  apply MethodRunSpec.step (by rfl) (recv_one_step m recv name arg hplain)
  apply (he origin m hm).bind hm.method.rootClean (prim_catchFree _ rfl)
  intro a n hn
  cases a with
  | val v =>
    have active := hm.after hn
    have saved := hr.after hm hn.1
    have h := callback_invokeWith (m := deliverA (.val v) n [])
      (active.reCtl (.value v) []) ⟨saved.block, saved.klass⟩ hp
      (denM_deliverA.mpr hn.2.1) ht hfree hname rfl
      (start := deliverA (.val v) n [.argsK recv site name [] [] .none]) (by rfl) (by rfl)
    exact h.erase.rebase (hn.1.trans (.ordinary (Framed_reCtl _ _ _)))
  | esc j =>
    apply MethodRunSpec.step (next := deliverA (.esc j) n []) (by rfl) (by cases j <;> rfl)
    apply MethodRunSpec.answer (a := .esc j) (n := n)
    exact ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩

/-- Sorbet 0.6.13405 accepts `b.call((b = nil; 5))` under an Integer Proc contract,
but rejects `b = nil; b.call(5)` (clink 240). The saved receiver is the checked block;
argument typing may change the local without changing the pending call's target. -/
theorem bound_callback_call_run {κ : Ctx} {Γ Γm Γm' : Env} {I σ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m : Machine}
    {localName name param : String} {arg : Checker.Expr}
    (hm : MethodActivation cb fr Γm origin m)
    (hr : MethodCallbackReceiver m (m.getLocal localName))
    (he : SemMethod cb fr Γm arg σ Γm') (hp : cb.params = [(param, σ)])
    (ht : activationReturnB Γm' = true) (hplain : plainArgB arg = true)
    (hfree : nameFreeN κ name = true) (hname : procCallNameB name = true) :
    MethodRunSpec m (evalFrom m (.send (some (.var .lvar localName)) name [arg] none))
      Γ Γm' cb.ret κ (callbackMethodCtx κ fr cb.code) I I := by
  apply MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.recvK name [toRuby arg] .none .explicit] (evalFrom m (.var .lvar localName))) from rfl)
  apply MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (deliverA (.val (m.getLocal localName)) m [.recvK name [toRuby arg] .none .explicit]) from by
      simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl,
        List.nil_append] using step_var_ctl (m := pushK [.recvK name [toRuby arg] .none .explicit]
        (evalFrom m (.var .lvar localName))) (x := localName) rfl)
  exact saved_callback_call_run hm hr he hp ht hplain hfree hname

#print axioms MethodCallbackReceiver.after
#print axioms saved_callback_call_run
#print axioms bound_callback_call_run

end Checker.Soundness.Typed
