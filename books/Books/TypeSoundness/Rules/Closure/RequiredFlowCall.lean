import Books.TypeSoundness.Rules.Closure.FlowSend
import Books.TypeSoundness.Rules.Closure.FlowCall
import Books.TypeSoundness.Rules.Closure.ReturnState

/-! Required-positional closure calls check the body at actual argument and live capture
types. Sorbet 0.6.13405 checks lambda/Proc arity but infers untyped parameters/results for
`->(x) { x + 1 }` (clink 218); that inference is not a safety premise here. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem required_closure_finish {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {ps : List SigParam}
    {facts : LocalFacts} {names : List String} {code : ClosureCode} {name : String}
    {m : Machine} {v : Value} {cl : Closure} {args : List Value} (site : SendSite)
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hf : LocalFactsOk facts m)
    (hproc : procClosure? m.heap v = some cl) (hcode : ClosureMatches code cl)
    (hcap : cl.captured = some (m.stack.headD 0)) (hklass : classOf m.heap v = Boot.procId)
    (hargs : DenAll (ps.map (·.2)) m args)
    (hc : closureMainB κ I = true) (hfree : nameFreeN κ name = true)
    (hp : code.params = ps.map (fun p => Checker.Param.req p.1)) (hname : procCallNameB name = true)
    (hin : activationEnvB (ps ++ blockLocals code.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true) (ht : FirstOrder τ = true)
    (hn : facts.captureNames? (withoutNames (ps.map (·.1) ++ code.locals) Γb) = some names)
    (hb : SemSafeCtxA (closureBodyCtx κ) (ps ++ blockLocals code.locals ++ Γ) I
      code.body τ (closureBodyCtx κ) Γb I) :
    StepSpec m (closureReturnEnv (ps.map (·.1) ++ code.locals) names Γ Γb) τ
      (Interp.finishSend m v site name args .none) κ I := by
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hc
  obtain ⟨hr, hw, hclass, hasm, hself, hblock, hconst, hi⟩ := hc
  have hi' p (hp : p ∈ ps ++ blockLocals code.locals ++ Γ) := List.all_eq_true.mp hin p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi'
  have hparams : cl.params = (ps.map (·.1)).map RubyCore.Param.req :=
    hcode.1.trans (by rw [hp]; exact toRubyParams_required ps)
  have hlen : args.length = (ps.map (·.1)).length := by
    simpa using denAll_length hargs
  have hu : RootUncaptured m := by
    rw [RootUncaptured, ← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime hr).captured
  have henv := currentClosureFrame_envOk hm (hm.runtime hr).captured hcap hargs
    (by simpa only [hcode.2.1] using (fun p hp => (hi' p hp).2))
    (by
      intro p hp v hv
      exact activationStable_heap (m := m) (hi' p (by simpa only [hcode.2.1] using hp)).1 rfl hv)
  have hstate := requiredClosureFrame_state_of_env hm
    (ReframeFO.empty hi hself hblock hconst) hasm (ClosureScopeEq.current hm.frameInRange hcap)
    (by rw [hcap]; exact hm.toStateCore.captureLive) henv
    (fun x => (constGet?_empty (κ := κ.withFrame none) hconst x).trans
      (constGet?_empty hconst x).symm)
  rw [hcode.2.1] at hstate
  change StepSpec m _ τ (Interp.invoke m v site name args none []) κ I
  rw [invoke_proc_dispatch hproc (hm.procDispatch hfree hname) hname hklass args site,
    callClosure_required m cl (ps.map (·.1)) args _ none none hparams hlen
      hcode.2.2.2.2.1 hcode.2.2.2.2.2, hcode.2.2.1]
  simp only [StepSpec, Interp.withKont, pushMethodFrame, hk]
  change RunSpec m (pushK [.blkFrameK m.frames.size cl.lam
    (closureBrk m cl (Interp.blockOwner m v)) cl args]
    (evalFrom (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) code.body))
    (closureReturnEnv (ps.map (·.1) ++ code.locals) names Γ Γb) τ κ I
  apply closure_return_main_runSpec (κb := closureBodyCtx κ) hm (ReframeFO.empty hi hself hblock hconst)
    hasm hr hw hclass
    (fun x => (constGet?_empty (κ := closureBodyCtx κ) hconst x).trans
      (constGet?_empty (κ := returnScopeCtx κ (closureBodyCtx κ)) hconst x).symm)
    hcap rfl (captureNames_sound hf hn)
    (by intro x; simpa only [hcode.2.1] using requiredClosureFrame_slots m cl (ps.map (·.1)) args hlen x)
    cl.lam _ cl args ht (hb _ hstate)
  · intro n hfr x σ hx v hv
    obtain ⟨y, hy⟩ := envGet?_mem hx
    exact denM_stripAlias.mpr (activationStable_framed
      (hi' (y, σ) (List.mem_append_right _ hy)).1
      (closure_pop_framed hm.frameInRange.2 hu hcap hfr hm.headAlias rfl) (denM_stripAlias.mp hv))
  · intro n _ x σ hx _ v hv
    obtain ⟨y, hy⟩ := envGet?_mem hx
    exact activationStable_heap (m := n) (List.all_eq_true.mp hout (y, σ) hy) rfl hv

/-- Source-level receiver/argument composition; required lambda/Proc arity follows the measured
Sorbet contracts in clinks 218/222. The checked body supplies the actual result type. -/
theorem SemFlow.requiredCall {κ κr κa : Ctx} {Γ Γr Γa Γb : Env}
    {I Ir Ia τ cap selfT : Ty} {facts fr fa : LocalFacts} {names : List String}
    {recv : Checker.Expr} {args : List Checker.Expr} {ps : List SigParam} {code : ClosureCode} {name : String}
    (hr : SemFlow κ Γ I facts recv (.clos code cap selfT) true κr Γr Ir fr)
    (ha : SemFlowAll κr Γr Ir fr args (ps.map (·.2)) κa Γa Ia fa)
    (hargs : ∀ σ ∈ ps.map (·.2), FirstOrder σ = true)
    (hc : closureMainB κa Ia = true) (hfree : nameFreeN κa name = true)
    (hp : code.params = ps.map (fun p => Checker.Param.req p.1)) (hname : procCallNameB name = true)
    (hin : activationEnvB (ps ++ blockLocals code.locals ++ Γa) = true)
    (hout : activationReturnB Γb = true) (ht : FirstOrder τ = true)
    (hn : fa.captureNames? (withoutNames (ps.map (·.1) ++ code.locals) Γb) = some names)
    (hb : SemSafeCtxA (closureBodyCtx κa) (ps ++ blockLocals code.locals ++ Γa) Ia
      code.body τ (closureBodyCtx κa) Γb Ia) :
    SemFlow κ Γ I facts (.send (some recv) name args none) τ false κa
      (closureReturnEnv (ps.map (·.1) ++ code.locals) names Γa Γb) Ia .unknown :=
  hr.sendRun ha hargs (fun _ hm hk hf site _ _ hproc hcode hcap hklass _ hargs =>
    required_closure_finish site hm hk hf hproc hcode hcap hklass hargs hc hfree hp hname hin hout ht hn hb)

#print axioms required_closure_finish
#print axioms SemFlow.requiredCall
end Checker.Soundness.Typed
