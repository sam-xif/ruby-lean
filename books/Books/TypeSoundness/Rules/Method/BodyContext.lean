import Books.TypeSoundness.Rules.Method.BodyYield
import Books.TypeSoundness.Rules.Method.MethodPres

/-! A checked callback and the two-frame method activation it can run in. The callback
certificate proves its body and capture fixed point; its arrow type alone supplies neither.
These semantic inputs will be supplied by definition/call checking, not by signatures. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

structure CheckedCallback (κ : Ctx) (Γ : Env) (I : Ty) where
  code : ClosureCode
  params : List SigParam
  ret : Ty
  names : List String
  out : Env
  required : code.params = params.map (fun p => Checker.Param.req p.1)
  main : closureMainB κ I = true
  returnFO : FirstOrder ret = true
  inputTypes : activationEnvB (params ++ blockLocals code.locals ++ Γ) = true
  outputTypes : activationReturnB out = true
  fixed : closureReturnEnv (params.map (·.1) ++ code.locals) names Γ out = Γ
  body : SemSafeCtxA (closureBodyCtx κ) (params ++ blockLocals code.locals ++ Γ) I
    code.body ret (closureBodyCtx κ) out I

theorem CheckedCallback.mainRuntime {κ : Ctx} {Γ : Env} {I : Ty} (cb : CheckedCallback κ Γ I) :
    κ.scope.runtimeMain = true := by
  have h := cb.main
  simp only [closureMainB, Bool.and_eq_true, and_assoc] at h
  exact h.1

theorem CheckedCallback.callerTypes {κ : Ctx} {Γ : Env} {I : Ty} (cb : CheckedCallback κ Γ I) :
    activationReturnB Γ = true := by
  apply List.all_eq_true.mpr
  intro p hp
  have h := List.all_eq_true.mp cb.inputTypes p (List.mem_append_right _ hp)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  have he : stripAlias p.2 = p.2 := by cases hτ : p.2 <;> simp_all [stripAlias, isAliasTy]
  simpa only [he] using h.1

structure MethodActivation {κ : Ctx} {Γ : Env} {I : Ty} (cb : CheckedCallback κ Γ I)
    (fr : Checker.Frame) (Γm : Env) (origin m : Machine) : Prop where
  originState : StateOk κ Γ I origin
  method : StateOk (callbackMethodCtx κ fr cb.code) Γm I m
  scope : CallbackMethodScope m
  fresh : origin.frames.size ≤ m.stack.headD 0
  framed : Framed origin (popMethodFrame m)
  callback : ∃ o cl, m.currentFrame.blk = some (.ref o) ∧ (m.heap.get o).payload = .proc cl ∧
    ClosureMatches cb.code cl ∧ CallbackCaller κ Γ I cl cb.params cb.names cb.out m

theorem MethodActivation.caller {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m : Machine}
    (h : MethodActivation cb fr Γm origin m) : StateOk κ Γ I (popMethodFrame m) := by
  obtain ⟨_, _, _, _, _, hc⟩ := h.callback
  exact hc.state

theorem MethodActivation.uncaptured {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m : Machine}
    (h : MethodActivation cb fr Γm origin m) : RootUncaptured m := by
  rw [RootUncaptured, rootFrame_eq_currentFrame h.method.frameInRange.1]
  exact h.scope.uncaptured

theorem MethodActivation.originUncaptured {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m : Machine}
    (h : MethodActivation cb fr Γm origin m) : RootUncaptured origin := by
  rw [RootUncaptured, rootFrame_eq_currentFrame h.originState.frameInRange.1]
  exact (h.originState.runtime cb.mainRuntime).captured

theorem MethodActivation.distinct {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m : Machine}
    (h : MethodActivation cb fr Γm origin m) :
    m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0 := by
  rw [h.framed.stack]
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h.originState.frameInRange.2 h.fresh)

theorem MethodActivation.after {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m n : Machine} {v : Value}
    (h : MethodActivation cb fr Γm origin m)
    (hr : MethodResultOk m Γ Γm' τ κ (callbackMethodCtx κ fr cb.code) I I (.val v) n) :
    MethodActivation cb fr Γm' origin n := by
  refine ⟨h.originState, (hr.2.2 v rfl).2,
    hr.1.methodScope h.method.frameInRange h.caller.frameInRange h.distinct h.scope,
    by rw [hr.1.stack]; exact h.fresh,
    hr.1.project h.originState.frameInRange h.originUncaptured h.originState.headAlias
      h.method.frameInRange h.uncaptured h.fresh h.framed, ?_⟩
  obtain ⟨o, cl, hblk, hproc, hcode, hc⟩ := h.callback
  exact ⟨o, cl, (congrArg FrameScope.blk (hr.1.scope h.method.frameInRange)).trans hblk,
    hr.1.proc hproc, hcode, hc.afterMethod hr.1 h.distinct (hr.2.2 v rfl).1⟩

theorem MethodActivation.reCtl {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m : Machine}
    (h : MethodActivation cb fr Γm origin m) (c : Ctl) (K : List Kont) :
    MethodActivation cb fr Γm origin (Checker.Soundness.reCtl m c K) := by
  refine ⟨h.originState, StateOk_reCtl h.method c K,
    ⟨h.scope.self, h.scope.cref, h.scope.owner, h.scope.uncaptured, h.scope.unaliased⟩, h.fresh,
    h.framed.trans (Framed_reCtl _ c K), ?_⟩
  obtain ⟨o, cl, hblk, hproc, hcode, hc⟩ := h.callback
  refine ⟨o, cl, hblk, hproc, hcode, ?_, hc.capture, hc.slots⟩
  simpa only [popMethodFrame, Checker.Soundness.reCtl] using (StateOk_reCtl hc.state c K)

theorem RunSpec.inMethod {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m start : Machine}
    (h : RunSpec m start Γm' τ (callbackMethodCtx κ fr cb.code) I)
    (hm : MethodActivation cb fr Γm origin m) :
    MethodRunSpec m start Γ Γm' τ κ (callbackMethodCtx κ fr cb.code) I I :=
  h.methodOrdinary hm.originState hm.caller hm.uncaptured cb.main cb.callerTypes hm.fresh hm.framed

/-- Method-local flow typing with a checked callback. Sorbet 0.6.13405 accepts local
retyping around repeated yields and stable captured writes (clinks 232–234). Every result
retains full caller/method states; this semantic judgment is not yet a checker rule. -/
def SemMethod {κ : Ctx} {Γ : Env} {I : Ty} (cb : CheckedCallback κ Γ I) (fr : Checker.Frame)
    (Γm : Env) (e : Checker.Expr) (τ : Ty) (Γm' : Env) : Prop :=
  ∀ origin m, MethodActivation cb fr Γm origin m →
    MethodRunSpec m (evalFrom m e) Γ Γm' τ κ (callbackMethodCtx κ fr cb.code) I I

theorem SemMethod.ordinary {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {e : Checker.Expr}
    (h : SemSafeCtxA (callbackMethodCtx κ fr cb.code) Γm I e τ
      (callbackMethodCtx κ fr cb.code) Γm' I) : SemMethod cb fr Γm e τ Γm' :=
  fun _ _ hm => h.methodOrdinary hm.originState hm.caller hm.method hm.uncaptured
    cb.main cb.callerTypes hm.fresh hm.framed

theorem SemMethod.seq {κ : Ctx} {Γ Γm Γm' Γm'' : Env} {I σ τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {e e' : Checker.Expr}
    (h : SemMethod cb fr Γm e σ Γm') (h' : SemMethod cb fr Γm' e' τ Γm'') :
    SemMethod cb fr Γm (.seq [e, e']) τ Γm'' :=
  fun origin m hm => (h origin m hm).seq hm.method.rootClean (fun n _ hr => h' origin n (hm.after hr))

theorem SemMethod.methodReturn {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {e : Checker.Expr}
    (h : SemMethod cb fr Γm e τ Γm') (ht : FirstOrder τ = true)
    {origin m : Machine} (hm : MethodActivation cb fr Γm origin m) (fid : FrameId) :
    RunSpec origin (pushK [.frameK fid] (evalFrom m e)) Γ τ κ I :=
  (h origin m hm).methodReturn hm.originState.frameInRange hm.originUncaptured
    hm.method.frameInRange hm.uncaptured hm.fresh hm.framed ht fid hm.originState.headAlias
    hm.originState.rootClean

#print axioms MethodActivation.after
#print axioms RunSpec.inMethod
#print axioms SemMethod.ordinary
#print axioms SemMethod.seq
#print axioms SemMethod.methodReturn
end Checker.Soundness.Typed
