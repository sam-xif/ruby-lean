import Books.TypeSoundness.Rules.Singleton.SingletonDispatch
import Books.TypeSoundness.Rules.Instance.CallWorld

/-! Execute an annotation-checked singleton body through the actual send/entry/return path. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem resolved_singleton_run {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {m : Machine}
    {cn name : String} {site : SendSite} {k e : ObjId} {md : MethodDef} {bodyExpr : Checker.Expr}
    {args : List Value} {ps : List SigParam}
    (hparams : md.params = (ps.map (·.1)).map RubyCore.Param.req) (hbody : md.body = toRuby bodyExpr)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hτ : FirstOrder τ = true)
    (body : SemSafeCtxA (singletonBodyCtx κ cn name) ps .ivar0 bodyExpr τ
      (singletonBodyCtx κ cn name) Γb .ivar0)
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (classSite : InstanceSite κ cn k m.heap) (he : (m.heap.get k).eigen = some e)
    (hw : CallWorld κ) (hkont : m.kont = []) (code : SingletonMethodCode k e md)
    (hu : md.undefined = false) (hl : lookup m.heap (.ref k) name = some (e, md))
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hk : ∀ x, constGet? (singletonBodyCtx κ cn name) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hn : DirectSendName name) :
    ∃ next, Interp.finishSend m (.ref k) site name args .none = .next next ∧
      RunSpec m next Γ τ κ I := by
  let f := requiredFrame (.ref k) name md (ps.map (·.1)) args
  have hentry := singleton_enter_state hm ht ha classSite he code (call_world_phase hm hw)
    hlen hargs hps hk
  have hrun := methodFrame_runSpec hm.frameInRange.2 (f := f) rfl hτ (body _ hentry)
    (fun n v result => singleton_call_pop_state hm ht ha hw rfl hk hΓ
      result.1 (result.2.2 v rfl))
  have henter : Interp.enterUserMethod m (.ref k) name md args none =
      .next (pushK [.frameK m.frames.size] (evalFrom (pushMethodFrame m f) bodyExpr)) := by
    rw [enterUserMethod_required m (.ref k) name md (ps.map (·.1)) args
      hparams code.captured code.declared (by simpa using hlen) code.fromBlock code.forTargets]
    simp only [Interp.withKont, pushK, evalFrom, f, pushMethodFrame, hkont, hbody, List.nil_append]
  exact ⟨_, (finishSend_singleton he (classSite.eigen_front he) hl code hu hn).trans henter, hrun hm.rootClean⟩

#print axioms resolved_singleton_run
end Checker.Soundness.Typed
