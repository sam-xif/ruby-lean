import Denote.Sem.MemberDeclared
import Denote.Typed.InstancePublish

/-! Full definition-state transport with input guards, not assumed outgoing class facts.
This installs code only; body annotations are the definition rule's separate obligation. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem StateOk_install_member {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {c : Cls} {d : Defn}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeClass = some c.name) (hc : c ∈ κ.classes)
    (ht : ReframeFO κ I) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hplain : unqualifiedClassB c.name = true) (hroot : c.name ∉ rootAncestors)
    (hf : memberFreshB κ c d = true) (htab : memberTableFrameB κ.classes c d = true)
    (hnew : "new" ≠ d.name) (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name) :
    StateOk (instanceDeclCtx κ c d) Γ I (installMethod m d.name (toRubyParams d.params) (toRuby d.body)) := by
  obtain ⟨k, ready⟩ := hm.classRuntime c.name hr
  obtain ⟨j, site⟩ := hm.classSites.of_scope hr
  have hj : j = k := Option.some.inj (site.named.symm.trans ready.named)
  subst j
  have howner := memberFreshB_sound hm hc ready.named hf
  have hcode := scoped_defined_instanceCode (name := d.name) (ps := toRubyParams d.params)
    (code := toRuby d.body) ready
  have hs : ClassesOk [c] m := by
    intro old ho
    have he := List.mem_singleton.mp ho
    subst old
    exact hm.classes c hc
  unfold installMethod
  rw [ready.owner]
  exact StateOk_publish_instance hm ht hΓ ha hs ready.named site
    (declared_not_object hm ready.named hroot) (howner c hc ready.named) howner
    rfl rfl rfl hcode hmiss hquiet
    ((hm.nested.publish_member hplain).methodWrite)
    ((hm.declCls.methodWrite hnew hmiss).publish_member hc (declLookupFrameB_sound htab))
    (hm.ownNames.publish_instance hc
      (memberOwnersB_sound hm hc ready.named (memberFreshB_owners hf)))
    ((hm.classChains.publish_member hc (declLookupFrameB_sound htab)).methodWrite)

theorem step_member_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {c : Cls} {d : Defn}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeClass = some c.name) (hc : c ∈ κ.classes)
    (ht : ReframeFO κ I) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hplain : unqualifiedClassB c.name = true) (hroot : c.name ∉ rootAncestors)
    (hf : memberFreshB κ c d = true) (htab : memberTableFrameB κ.classes c d = true)
    (hnew : "new" ≠ d.name) (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name)
    (hctl : m.ctl = .eval (.def' d.name (toRubyParams d.params) (toRuby d.body))) :
    ∃ n, Interp.stepFn m = .next n ∧ StateOk (instanceDeclCtx κ c d) Γ I n := by
  obtain ⟨k, ready⟩ := hm.classRuntime c.name hr
  have hs := StateOk_install_member hm hr hc ht hΓ ha hplain hroot hf htab hnew hmiss hquiet
  exact ⟨_, step_def_install hctl (defHookQuiet_install hquiet (scoped_defHookQuiet ready)),
    StateOk_reCtl hs (.value (.sym d.name)) _⟩

#print axioms StateOk_install_member
#print axioms step_member_state
end Ratchet.Denote.Typed
