import Denote.Typed.InstanceInstall
import Denote.Sem.InstanceTable

/-! Connect actual def installation to the positive class record. Body safety is not
claimed here: the class judgment must additionally consume its annotation-checked body. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem step_instance_publish {C : CTable} {c : Cls} {d : Defn} {m : Machine} {cls : ObjId}
    (hC : ClassesOk C m) (hc : ClassesOk [c] m) (hk : classNamed? m.heap c.name = some cls)
    (hf : ∀ old ∈ c.methods, old.name ≠ d.name)
    (hs : ∀ old ∈ C, classNamed? m.heap old.name = some cls →
      ∀ method ∈ old.methods, method.name ≠ d.name)
    (ho : m.currentFrame.defmod = cls) (hcref : m.currentFrame.cref = [cls, Boot.objectId])
    (hkind : m.currentFrame.kind = .classBody) (hv : m.currentFrame.defVis = .pub)
    (hp : m.preludeMode = false)
    (hh : DefHookQuiet (installMethod m d.name (toRubyParams d.params) (toRuby d.body)))
    (hctl : m.ctl = .eval (.def' d.name (toRubyParams d.params) (toRuby d.body))) :
    ∃ n, Interp.stepFn m = .next n ∧ ClassesOk (classWithMethod c d :: C) n := by
  refine ⟨_, step_def_install hctl hh, ?_⟩
  change ClassesOk _ (installMethod m d.name (toRubyParams d.params) (toRuby d.body))
  have hcode := definedMethod_instanceCode (name := d.name) (ps := toRubyParams d.params)
    (body := toRuby d.body) ho hcref hkind hv hp
  unfold installMethod
  rw [ho]
  exact ClassesOk_publish_instance hC hc hk hf hs rfl rfl rfl hcode

#print axioms step_instance_publish

/-- The scope request discharges all physical installation premises from incoming
conformance. Constructor/nested contracts and annotation-checked bodies are not invented. -/
theorem step_scoped_instance_state {κ : Ctx} {Γ : Env} {I : Ty} {c : Cls} {d : Defn}
    {m : Machine} (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeClass = some c.name)
    (ht : ReframeFO κ I) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hc : ClassesOk [c] m)
    (hobj : m.currentFrame.defmod ≠ Boot.objectId)
    (hf : ∀ old ∈ c.methods, old.name ≠ d.name)
    (hs : ∀ old ∈ κ.classes, classNamed? m.heap old.name = some m.currentFrame.defmod →
      ∀ method ∈ old.methods, method.name ≠ d.name)
    (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name)
    (hnested : NestedClassesOk (classWithMethod c d :: κ.classes)
      (installMethod m d.name (toRubyParams d.params) (toRuby d.body)))
    (hdecl : DeclClassOk (instanceDeclCtx κ c d)
      (installMethod m d.name (toRubyParams d.params) (toRuby d.body)))
    (hctl : m.ctl = .eval (.def' d.name (toRubyParams d.params) (toRuby d.body))) :
    ∃ n, Interp.stepFn m = .next n ∧ StateOk (instanceDeclCtx κ c d) Γ I n := by
  obtain ⟨k, hk⟩ := hm.classRuntime c.name hr
  have ready : ClassScopeAt c.name m.currentFrame.defmod m := hk.owner.symm ▸ hk
  have hp : StateOk (instanceDeclCtx κ c d) Γ I
      (installMethod m d.name (toRubyParams d.params) (toRuby d.body)) :=
    StateOk_publish_instance hm ht hΓ ha hc ready.named hobj hf hs rfl rfl rfl
      (scoped_defined_instanceCode ready) hmiss hquiet hnested hdecl
  refine ⟨_, step_def_install hctl (defHookQuiet_install hquiet (scoped_defHookQuiet ready)), ?_⟩
  exact StateOk_reCtl hp (.value (.sym d.name)) _

#print axioms step_scoped_instance_state
end Ratchet.Denote.Typed
