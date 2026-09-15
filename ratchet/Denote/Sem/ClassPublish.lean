import Ratchet.ClassHeader
import Denote.Sem.State

/-! Ghost publication of an executed empty class record at its existing lexical site.
The record's ancestry/dispatch/allocator facts must already be proved; no method body or
callable signature is introduced here. Default and explicit-superclass headers share this. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem StateOk_publish_empty_class {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {c : Cls}
    (hm : StateOk κ Γ I m) (hs : κ.scope.runtimeClass = some c.name)
    (hempty : c.methods = []) (_hsingle : c.smethods = []) (hn : unqualifiedClassB c.name = true)
    (hd : DeclClassOk { κ with pos := { κ.pos with
      classes := c :: κ.classes
      plainAlloc := c.name :: κ.pos.plainAlloc } } m)
    (ha : ∃ k, classNamed? m.heap c.name = some k ∧ PlainAllocator m.heap k)
    (hown : ClassOwnNames (c :: κ.classes) m.heap)
    (hchain : ClassChains (c :: κ.classes) m.heap) :
    StateOk { κ with pos := { κ.pos with
      classes := c :: κ.classes
      plainAlloc := c.name :: κ.pos.plainAlloc } } Γ I m := by
  obtain ⟨k, site⟩ := hm.classSites.of_scope hs
  refine { hm with
    classes := ?_
    ownNames := hown
    classChains := hchain
    classSites := ?_
    allocators := ?_
    nested := ?_
    declCls := hd }
  · apply hm.classSites.recontext (κ' := { κ with pos := { κ.pos with
      classes := c :: κ.classes
      plainAlloc := c.name :: κ.pos.plainAlloc } }) _ (fun _ h => h)
    intro cn hcn
    change cn ∈ c.name :: (κ.classes.map (·.name) ++ κ.scope.runtimeClass.toList) at hcn
    rcases List.mem_cons.mp hcn with rfl | hcn
    · simp [classSiteNames, hs]
    · exact hcn
  · intro cn hcn
    change cn ∈ c.name :: κ.pos.plainAlloc at hcn
    rcases List.mem_cons.mp hcn with rfl | hcn
    · exact ha
    · exact hm.allocators cn hcn
  · intro old hold
    change old ∈ c :: κ.classes at hold
    rcases List.mem_cons.mp hold with rfl | hold
    · exact ⟨k, site.named, by simp [hempty]⟩
    · exact hm.classes old hold
  · intro owner leaf old hold
    have hne := unqualifiedClassB_ne_path hn owner leaf
    change clsGet? (c :: κ.classes) (owner ++ "::" ++ leaf) = some old at hold
    simp only [clsGet?, List.find?_cons, beq_eq_false_iff_ne.mpr hne] at hold
    exact hm.nested owner leaf old hold

#print axioms StateOk_publish_empty_class
end Ratchet.Denote
