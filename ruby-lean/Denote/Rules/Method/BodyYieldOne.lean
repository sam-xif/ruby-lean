import Denote.Rules.Method.BodyContext

/-! Yield evaluates its argument before entering the checked callback. Sorbet checks
the resulting type against the declared Proc parameter (0.6.13405, clink 234). The
argument may itself assign method locals or invoke the same callback. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemMethod.yieldOne {κ : Ctx} {Γ Γm Γm' : Env} {I σ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Ratchet.Frame} {name : String} {arg : Ratchet.Expr}
    (h : SemMethod cb fr Γm arg σ Γm') (hp : cb.params = [(name, σ)])
    (ht : activationReturnB Γm' = true) (hplain : Plain arg) :
    SemMethod cb fr Γm (.yield' [arg]) cb.ret Γm' := by
  intro origin m hm
  apply MethodRunSpec.step (answerPoint_evalFrom _ _) (show Interp.stepFn _ = .next
    (pushK [.yieldArgK [] []] (evalFrom m arg)) from by
      cases arg <;> first | rfl | exact False.elim hplain)
  apply (h origin m hm).bind (by
    intro k hk tag
    simp only [List.mem_singleton] at hk
    subst k; simp)
  intro a n hr
  cases a with
  | esc j =>
    obtain ⟨exc, rfl, _⟩ := hr.2.1.only_raise
    apply MethodRunSpec.step (next := deliverA (.esc (.raiseJ exc)) n []) (by rfl) (by rfl)
    apply MethodRunSpec.answer (a := .esc (.raiseJ exc)) (n := n)
    exact ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩
  | val v =>
    have hn := hm.after hr
    obtain ⟨o, cl, hblk, hproc, hcode, hc⟩ := hn.callback
    let base := deliverA (.val v) n []
    have hc' : CallbackCaller κ Γ I cl cb.params cb.names cb.out base :=
      ⟨by simpa only [base, popMethodFrame, deliverA] using
        (StateOk_deliverA (a := .val v) (K := []) hc.state), hc.capture, hc.slots⟩
    have hs' : CallbackMethodScope base := ⟨hn.scope.self, hn.scope.cref, hn.scope.owner, hn.scope.uncaptured⟩
    have hσ : activationStableB σ = true := by
      have hi := cb.inputTypes
      rw [hp] at hi
      have first := List.all_eq_true.mp hi (name, σ) (by simp)
      simp only [Bool.and_eq_true] at first
      exact first.1
    have hparams : cl.params = (cb.params.map (·.1)).map RubyCore.Param.req :=
      hcode.1.trans (by rw [cb.required]; exact toRubyParams_required cb.params)
    have hlen : [v].length = cb.params.length := by rw [hp]; rfl
    have hargs : DenAll (cb.params.map (·.2)) (popMethodFrame base) [v] := by
      rw [hp]
      exact ⟨activationStable_heap (m := n) hσ rfl hr.2.1, trivial⟩
    have hstep := doYield_required base cl o (cb.params.map (·.1)) [v] cb.code.body []
      rfl hblk hproc hparams hcode.2.2.1 (by simpa only [List.length_map] using hlen)
    apply MethodRunSpec.step (by rfl) (show Interp.stepFn (deliverA (.val v) n [.yieldArgK [] []]) =
      .next _ from hstep)
    exact (checked_callback_method_run hc' (StateOk_deliverA hn.method) hs' hn.distinct hlen hargs
      cb.main cb.returnFO (by simpa only [hcode.2.1] using cb.inputTypes) cb.outputTypes ht
      (by simpa only [hcode.2.1] using cb.fixed) (by simpa only [hcode.2.1] using cb.body)).rebase
      (hr.1.trans (.ordinary (Framed_reCtl _ _ _)))

theorem SemMethod.yieldInt {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Ratchet.Frame} {name : String}
    (hp : cb.params = [(name, .int)]) (ht : activationReturnB Γm = true) (arg : Int) :
    SemMethod cb fr Γm (.yield' [.int arg]) cb.ret Γm :=
  (SemMethod.ordinary SemSafeCtxA.intLit).yieldOne hp ht trivial

#print axioms SemMethod.yieldOne
#print axioms SemMethod.yieldInt
end Ratchet.Denote.Typed
