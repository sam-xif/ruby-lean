import Denote.Rules.Singleton.SingletonInstall
import Denote.Sem.Singleton.SingletonTable

/-! Actual singleton installation publishes code into ClassesOk. This is independent of
the later body certificate and does not claim full outgoing scope/dispatch conformance. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem scoped_singleton_publish {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {d : Defn} (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes)
    (hr : κ.scope.runtimeClass = some c.name) (ht : κ.selfTy = some (.clsOf c.name))
    (hctl : m.ctl = .eval (.defs .self' d.name (toRubyParams d.params) (toRuby d.body)))
    (hf : ∀ old ∈ κ.classes, ∀ prev ∈ old.smethods, prev.name ≠ d.name) :
    ∃ k e, classNamed? m.heap c.name = some k ∧
      let n := installSingleton m e d.name (toRubyParams d.params) (toRuby d.body)
      Interp.stepFn m = .next (Interp.withCtl n (.value (.sym d.name))) ∧
      ClassesOk ({ c with smethods := d :: c.smethods } :: κ.classes) n := by
  obtain ⟨k, e, hk, _, he, step, code, _, _⟩ := scoped_singleton_install hm hr ht hctl
  exact ⟨k, e, hk, step, ClassesOk_publish_singleton hm.classes hm.classSites hc hk he
    (fun old ho _ _ _ => hf old ho) rfl rfl rfl code⟩

/-- Retained positive code plus the class site's front fact recovers actual dispatch
after arbitrary conformance-preserving evaluation, not just immediately after a def. -/
theorem classesOk_singleton_lookup {κ : Ctx} {m : Machine} {c : Cls} {d : Defn}
    (hm : ClassesOk κ.classes m) (sites : ClassSitesOk κ m.heap)
    (hc : c ∈ κ.classes) (hd : d ∈ c.smethods) :
    ∃ k e md, classNamed? m.heap c.name = some k ∧
      lookup m.heap (.ref k) d.name = some (e, md) ∧
      md.params = toRubyParams d.params ∧ md.body = toRuby d.body ∧
      md.undefined = false ∧ SingletonMethodCode k e md := by
  obtain ⟨k, hk, _, single⟩ := hm c hc
  obtain ⟨e, md, he, _, row, rest⟩ := single d hd
  obtain ⟨j, site⟩ := sites.of_class hc
  have hj : j = k := Option.some.inj (site.named.symm.trans hk)
  subst j
  obtain ⟨tail, ha⟩ := classFrontB_sound (site.eigen_front he)
  exact ⟨k, e, md, hk, lookup_own_first (by simpa only [classOf, he] using ha) row, rest⟩

#print axioms scoped_singleton_publish
#print axioms classesOk_singleton_lookup
end Ratchet.Denote.Typed
