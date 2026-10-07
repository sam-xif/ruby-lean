import Books.TypeSoundness.Rules.Singleton.SingletonPublish
import Books.TypeSoundness.Conformance.Singleton.SingletonContext

/-! Full outgoing conformance for singleton installation. Positive code, absence facts,
ancestry and root initialization are derived from the incoming state and static guards. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem StateOk_install_singleton {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {d : Defn} {k e : ObjId}
    (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes) (ready : ClassScopeAt c.name k m)
    (he : (m.heap.get k).eigen = some e)
    (ht : ReframeFO κ I) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hplain : unqualifiedClassB c.name = true)
    (hf : singletonFreshB κ.classes d = true) (htab : singletonTableFrameB κ.classes c d = true)
    (hnew : "new" ≠ d.name) (hmiss : "method_missing" ≠ d.name)
    (hquiet : "method_added" ≠ d.name) (hinit : "initialize" ≠ d.name)
    (hhook : classHookSelectors.contains d.name = false) :
    StateOk (singletonDeclCtx κ c d) Γ I
      (installSingleton m e d.name (toRubyParams d.params) (toRuby d.body)) := by
  have site := hm.classSites.at_class hc ready.named
  have hleaf : (m.heap.get e).eigen = none := by simpa only [classOf, he] using site.metaLeaf
  have hobj : e ≠ Boot.objectId := by
    intro h; subst e
    obtain ⟨oe, hoe, _⟩ := hm.core.classReady.objectEigen
    rw [hleaf] at hoe
    cases hoe
  have hsh : singletonHookName ≠ d.name := by
    intro he
    have : classHookSelectors.contains d.name = true := by rw [← he]; decide
    rw [hhook] at this; cases this
  have hnames : ¬d.name = "const_added" ∧ ¬d.name = "inherited" ∧ ¬d.name = "singleton_method_added" := by
    simpa [classHookSelectors] using hhook
  have hr : ReframeFO (reserveNameCtx κ d.name) I :=
    ⟨ht.spine, ht.self, ht.block, ht.consts, ht.paths⟩
  exact StateOk_methodWrite_tables (StateOk_reserveName hm d.name) hr hΓ ha
    (by simp [nameFreeN, reserveNameCtx, Ctx.declared]) hmiss hquiet hsh
    (ClassesOk_publish_singleton hm.classes hm.classSites hc ready.named he
      (fun old ho _ _ _ => singletonFreshB_sound hf old ho) rfl rfl rfl
      (definedSingleton_code ready _ _))
    (hm.classSites.publish_singleton hc hquiet hsh (fun h => hnames.2.1 h.symm))
    (DefsOk_methodWrite_other hm.defs hobj)
    ((hm.nested.publish_singleton hplain).methodWrite)
    ((hm.declCls.methodWrite hnew hmiss).publish_singleton hc (declLookupFrameB_sound htab))
    (hm.ownNames.publish_singleton hm.classSites hc hleaf)
    ((hm.classChains.publish_singleton hc (declLookupFrameB_sound htab)).methodWrite)
    (hm.rootInit.transport id (methodOn_defineMethod _ _ _ _ _ _ hinit))
    (primitiveInitB_defineMethod_other hm.primitiveInit hinit)
    (fun _ => Or.inl (by simpa only [classOf, he] using site.metaNotMain))
    (fun _ => Or.inr (by simp [classHookNames, hnames.1, hnames.2.1]))

theorem step_singleton_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {c : Cls} {d : Defn}
    (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes)
    (hr : κ.scope.runtimeClass = some c.name) (hself : κ.selfTy = some (.clsOf c.name))
    (ht : ReframeFO κ I) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hplain : unqualifiedClassB c.name = true)
    (hf : singletonFreshB κ.classes d = true) (htab : singletonTableFrameB κ.classes c d = true)
    (hnew : "new" ≠ d.name) (hmiss : "method_missing" ≠ d.name)
    (hquiet : "method_added" ≠ d.name) (hinit : "initialize" ≠ d.name)
    (hhook : classHookSelectors.contains d.name = false)
    (hctl : m.ctl = .eval (.defs .self' d.name (toRubyParams d.params) (toRuby d.body))) :
    ∃ n, Interp.stepFn m = .next n ∧ StateOk (singletonDeclCtx κ c d) Γ I n := by
  obtain ⟨k, e, hk, _, he, step, _, _, _⟩ := scoped_singleton_install hm hr hself hctl
  obtain ⟨j, ready⟩ := hm.classRuntime c.name hr
  have hj : j = k := Option.some.inj (ready.named.symm.trans hk)
  subst j
  exact ⟨_, step, StateOk_reCtl (StateOk_install_singleton hm hc ready he ht hΓ ha hplain
    hf htab hnew hmiss hquiet hinit hhook) _ _⟩

#print axioms StateOk_install_singleton
#print axioms step_singleton_state
end Checker.Soundness.Typed
