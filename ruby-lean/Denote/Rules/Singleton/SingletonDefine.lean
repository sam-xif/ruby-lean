import Denote.Rules.Singleton.SingletonState
import Denote.Rules.Singleton.SingletonEntry

/-! Execute def-self and publish full conformance. The body premise checks its annotated
domain even when the definition is never called; installation itself does not run it. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Sorbet 0.6.13405 rejects an uncalled factory with a String result against returns(Point)
(clink 184). The full-domain body premise remains mandatory even though def does not run it. -/
theorem SemSafeCtxA.singletonDecl {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam}
    (_hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (_hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (_hret : FirstOrder τ = true)
    (_hbody : SemSafeCtxA (singletonBodyCtx (singletonDeclCtx κ c d) c.name d.name)
      ps .ivar0 d.body τ (singletonBodyCtx (singletonDeclCtx κ c d) c.name d.name) Γb .ivar0)
    (hr : κ.scope.runtimeClass = some c.name) (hself : κ.selfTy = some (.clsOf c.name))
    (hc : c ∈ κ.classes) (ht : ReframeFO κ I)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (ha : κ.asms = [])
    (hplain : unqualifiedClassB c.name = true) (hf : singletonFreshB κ.classes d = true)
    (htab : singletonTableFrameB κ.classes c d = true)
    (hnew : "new" ≠ d.name) (hmiss : "method_missing" ≠ d.name)
    (hquiet : "method_added" ≠ d.name) (hinit : "initialize" ≠ d.name) :
    SemSafeCtxA κ Γ I (.defs .self' d.name d.params d.body) .sym (singletonDeclCtx κ c d) Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  obtain ⟨k, e, hk, _, he, hs, _, _, _⟩ := scoped_singleton_install
    (m := evalFrom m (.defs .self' d.name d.params d.body)) (StateOk_reCtl hm _ []) hr hself rfl
  obtain ⟨j, ready⟩ := hm.classRuntime c.name hr
  have hj : j = k := Option.some.inj (ready.named.symm.trans hk)
  subst j
  let n := installSingleton m e d.name (toRubyParams d.params) (toRuby d.body)
  refine ⟨n, .sym d.name, ?_, Framed_defineMethod m e d.name
    (definedSingleton m e (toRubyParams d.params) (toRuby d.body)),
    by simp [AnsOk, denM, isSymV], fun _ _ =>
      StateOk_install_singleton hm hc ready he ht hΓ ha hplain hf htab hnew hmiss hquiet hinit⟩
  simpa only [n, installSingleton, definedSingleton, evalFrom, toRuby, deliverA,
    Interp.withCtl, reCtl, Machine.currentFrame, Answer.ctl] using hs

#print axioms SemSafeCtxA.singletonDecl
end Ratchet.Denote.Typed
