import Books.TypeSoundness.Conformance.Names.MemberDeclared
import Books.TypeSoundness.Rules.Instance.InstancePublish

/-! Full definition-state transport with input guards, not assumed outgoing class facts.
This installs code only; body annotations are the definition rule's separate obligation. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem StateOk_install_member {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {c : Cls} {d : Defn}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeClass = some c.name) (hc : c ∈ κ.classes)
    (ht : ReframeFO κ I) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hplain : unqualifiedClassB c.name = true) (hroot : c.name ∉ rootAncestors)
    (hf : memberFreshB κ c d = true) (htab : memberTableFrameB κ.classes c d = true)
    (hnew : "new" ≠ d.name) (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name)
    (hauto : autoPrivateNames.contains d.name = false)
    (hhook : classHookSelectors.contains d.name = false) :
    StateOk (instanceDeclCtx κ c d) Γ I (installMethod m d.name (toRubyParams d.params) (toRuby d.body)) := by
  obtain ⟨k, ready⟩ := hm.classRuntime c.name hr
  obtain ⟨j, site⟩ := hm.classSites.of_scope hr
  have hj : j = k := Option.some.inj (site.named.symm.trans ready.named)
  subst j
  have howner := memberFreshB_sound hm hc ready.named hf
  have hcode := scoped_defined_instanceCode (name := d.name) (ps := toRubyParams d.params)
    (code := toRuby d.body) ready hm.frameInRange.1 hauto
  have hs : ClassesOk [c] m := by
    intro old ho
    have he := List.mem_singleton.mp ho
    subst old
    exact hm.classes c hc
  unfold installMethod
  rw [ready.owner]
  exact StateOk_publish_instance hm ht hΓ ha hs ready.named site
    (declared_not_object hm ready.named hroot) (howner c hc ready.named) howner
    (definedMethod_params ..) (definedMethod_body ..) (definedMethod_undefined ..) hcode hmiss hquiet
    (by
      intro he
      have : classHookSelectors.contains d.name = true := by rw [← he]; decide
      rw [hhook] at this; cases this)
    (by
      intro he
      have : classHookSelectors.contains d.name = true := by rw [← he]; decide
      rw [hhook] at this; cases this)
    ((hm.nested.publish_member hplain).methodWrite)
    ((hm.declCls.methodWrite hnew hmiss).publish_member hc (declLookupFrameB_sound htab))
    (hm.ownNames.publish_instance hc
      (memberOwnersB_sound hm hc ready.named (memberFreshB_owners hf)))
    ((hm.classChains.publish_member hc (declLookupFrameB_sound htab)).methodWrite)
    (hm.rootInit.write_outside (by
      rw [hm.core.classReady.objectChain]
      exact declared_not_root hm ready.named hroot))
    (fun _ => Or.inl ready.notMain)
    (fun _ => Or.inr (by
      have h' : ¬d.name = "const_added" ∧ ¬d.name = "inherited" ∧ ¬d.name = "singleton_method_added" := by
        simpa [classHookSelectors] using hhook
      simp [classHookNames, h'.1, h'.2.1]))

end Checker.Soundness.Typed
