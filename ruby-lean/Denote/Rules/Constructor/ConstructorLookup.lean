import Denote.Rules.Instance.InstanceResolve
import Denote.Rules.Method.MethodResolve
import Denote.Sem.Class.ClassNew

/-! Recover constructor dispatch and actual initializer code from published conformance.
Allocation shape and the initializer's annotation-domain proof remain separate obligations. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem methodOn_own_first {h : Heap} {k : ObjId} {rest : List ObjId} {name : String}
    {md : MethodDef} (ha : ancestors h k = k :: rest)
    (hm : (h.classPayload? k).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = some md)
    (hv : md.visibilityOnly = false) :
    Interp.methodOn h k name = some (k, md) := by
  unfold Interp.methodOn
  rw [ha]
  exact lookup_go_own hm hv

theorem declared_constructor_code {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {d : Defn} (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes) (hd : d ∈ c.methods)
    (hn : d.name = "initialize") (hnew : smroGet? κ.classes c.name "new" = none)
    (hkind : c.isModule = false) :
    ∃ k md, InstanceSite κ c.name k m.heap ∧
      NewDispatch m.heap (classOf m.heap (.ref k)) ∧
      md.params = toRubyParams d.params ∧ md.body = toRuby d.body ∧
      InstanceMethodCode k "initialize" md ∧
      Interp.methodOn m.heap k "initialize" = some (k, md) ∧ md.undefined = false := by
  obtain ⟨k, hk, hmethods, _⟩ := hm.classes c hc
  obtain ⟨j, site⟩ := hm.classSites.of_class hc
  have he : j = k := Option.some.inj (site.named.symm.trans hk)
  subst j
  obtain ⟨md, hfind, hp, hb, hu, code⟩ := hmethods d hd
  obtain ⟨rest, hrest⟩ := classFrontB_sound site.front
  have hlookup := methodOn_own_first hrest hfind code.visibilityOnly
  rw [hn] at hlookup code
  have hdispatch := (hm.declCls c hc k hk).2.2.2.2.1 hkind hnew
  exact ⟨k, md, site, ⟨hdispatch.1, hdispatch.2⟩, hp, hb, code, hlookup, hu⟩

#print axioms declared_constructor_code
end Ratchet.Denote.Typed
