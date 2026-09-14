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
end Ratchet.Denote.Typed
