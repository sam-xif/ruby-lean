import Denote.Rules.Instance.InstanceResolve
import Denote.Sem.Class.ClassNew

/-! Recover constructor dispatch and actual initializer code from published conformance.
Allocation shape and the initializer's annotation-domain proof remain separate obligations. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem methodOn_own_first {h : Heap} {k : ObjId} {rest : List ObjId} {name : String}
    {md : MethodDef} (ha : ancestors h k = k :: rest)
    (hm : (h.classPayload? k).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = some md) :
    Interp.methodOn h k name = some (k, md) := by
  unfold Interp.methodOn
  rw [ha, List.firstM]
  cases hc : h.classPayload? k with
  | none => simp [hc] at hm
  | some cp =>
    cases hf : cp.methods.find? (·.1 == name) with
    | none => simp [hc, hf] at hm
    | some p =>
      simp only [hc, Option.bind_some, hf, Option.map_some, Option.some.injEq] at hm
      simp only [hf, hm, Option.map_some]
      rfl

theorem declared_constructor_code {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {d : Defn} (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes) (hd : d ∈ c.methods)
    (hn : d.name = "initialize") (hnew : smroGet? κ.classes c.name "new" = none) :
    ∃ k md, InstanceSite κ c.name k m.heap ∧
      NewDispatch m.heap (classOf m.heap (.ref k)) ∧
      md.params = toRubyParams d.params ∧ md.body = toRuby d.body ∧
      InstanceMethodCode k "initialize" md ∧ Interp.userInit? m.heap k = some md := by
  obtain ⟨k, hk, hmethods⟩ := hm.classes c hc
  obtain ⟨j, site⟩ := hm.classSites.of_class hc
  have he : j = k := Option.some.inj (site.named.symm.trans hk)
  subst j
  obtain ⟨md, hfind, hp, hb, _, code⟩ := hmethods d hd
  obtain ⟨rest, hrest⟩ := classFrontB_sound site.front
  have hlookup := methodOn_own_first hrest hfind
  rw [hn] at hlookup code
  have hdispatch := (hm.declCls c hc k hk).2.2.2.2.1 hnew
  exact ⟨k, md, site, ⟨hdispatch.1, hdispatch.2⟩, hp, hb, code,
    by simp [Interp.userInit?, hlookup, code.builtin]⟩

#print axioms declared_constructor_code
end Ratchet.Denote.Typed
