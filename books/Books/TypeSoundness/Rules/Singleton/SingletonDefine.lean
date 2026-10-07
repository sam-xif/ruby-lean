import Books.TypeSoundness.Rules.Singleton.SingletonState
import Books.TypeSoundness.Rules.Singleton.SingletonEntry
import Books.TypeSoundness.Rules.Singleton.SingletonHook
import Books.TypeSoundness.Rules.Instance.MemberDefine

/-! Execute def-self and publish full conformance. The body premise checks its annotated
domain even when the definition is never called; installation itself does not run it. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

/-- Sorbet 0.6.13405 rejects an uncalled factory with a String result against returns(Point)
(clink 184). The full-domain body premise remains mandatory even though def does not run it. -/
theorem SemSafeCtxA.singletonDecl {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam}
    (_hparams : d.params = ps.map (fun p => Checker.Param.req p.1))
    (_hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (_hret : FirstOrder τ = true)
    (_hbody : SemSafeCtxA (singletonBodyCtx (singletonDeclCtx κ c d) c.name d.name)
      ps .ivar0 d.body τ (singletonBodyCtx (singletonDeclCtx κ c d) c.name d.name) Γb .ivar0)
    (hr : κ.scope.runtimeClass = some c.name) (hself : κ.selfTy = some (.clsOf c.name))
    (hc : c ∈ κ.classes) (ht : ReframeFO κ I)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (ha : κ.asms = [])
    (hplain : unqualifiedClassB c.name = true) (hf : singletonFreshB κ.classes d = true)
    (htab : singletonTableFrameB κ.classes c d = true)
    (hnew : "new" ≠ d.name) (hmiss : "method_missing" ≠ d.name)
    (hquiet : "method_added" ≠ d.name) (hinit : "initialize" ≠ d.name)
    (hhook : classHookSelectors.contains d.name = false) :
    SemSafeCtxA κ Γ I (.defs .self' d.name d.params d.body) .sym (singletonDeclCtx κ c d) Γ I := by
  intro m hm
  obtain ⟨k, e, hk, _, he, hs, _, _, _⟩ := scoped_singleton_install
    (m := evalFrom m (.defs .self' d.name d.params d.body)) (StateOk_reCtl hm _ []) hr hself rfl
  obtain ⟨j, ready⟩ := hm.classRuntime c.name hr
  have hj : j = k := Option.some.inj (ready.named.symm.trans hk)
  subst j
  have site := hm.classSites.at_class hc ready.named
  have hsh : singletonHookName ≠ d.name := by
    intro h
    have : classHookSelectors.contains d.name = true := by rw [← h]; decide
    rw [hhook] at this; cases this
  let md := definedSingleton m e (toRubyParams d.params) (toRuby d.body)
  let n := installSingleton m e d.name (toRubyParams d.params) (toRuby d.body)
  have hn : StateOk (singletonDeclCtx κ c d) Γ I n :=
    StateOk_install_singleton hm hc ready he ht hΓ ha hplain hf htab hnew hmiss hquiet hinit hhook
  have hstep : Interp.stepFn (evalFrom m (.defs .self' d.name d.params d.body)) =
      .next { n with
        ctl := .send (.ref k) .reflective "singleton_method_added" [.sym d.name] none [],
        kont := [.methodEditsK [] (.sym d.name)] } := by
    simpa only [n, installSingleton, definedSingleton, evalFrom, toRuby, currentFrame_reCtl,
      List.nil_append] using hs
  apply RunSpec.step (answerPoint_evalFrom _ _) hstep
  apply singleton_hook_runSpec hn (Framed_defineMethod m e d.name md)
  · change ((defineMethod m.heap e d.name md).classPayload? k).isSome = true
    rw [Proof.classPayload?_isSome_defineMethod]
    exact classNamed_payload ready.named
  · change singletonDefHookQuietB (defineMethod m.heap e d.name md) k = true
    simpa only [singletonDefHookQuietB, Proof.lookup_defineMethod m.heap e d.name singletonHookName md
      (.ref k) hsh (Proof.classOf_defineMethod ..)] using site.singletonHook

#print axioms SemSafeCtxA.singletonDecl
end Checker.Soundness.Typed
