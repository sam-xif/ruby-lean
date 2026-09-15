import Denote.Sem.MethodHeap

/-! Root initialization is preserved by writes outside its physical chain. A top-level
definition updates the existing def table; only initialize itself waives root absence. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem methodOn_defineMethod_outside {h : Heap} {cls k : ObjId} {name query : String} {md : MethodDef}
    (hn : cls ∉ ancestors h k) :
    Interp.methodOn (defineMethod h cls name md) k query = Interp.methodOn h k query := by
  have go : ∀ ks : List ObjId, cls ∉ ks →
      lookup.go (defineMethod h cls name md) query ks = lookup.go h query ks := by
    intro ks
    induction ks with
    | nil => intro _; rfl
    | cons j js ih =>
      intro hn
      have hj : j ≠ cls := fun he => hn (he ▸ List.mem_cons_self)
      have ht : cls ∉ js := fun hm => hn (List.mem_cons_of_mem j hm)
      simp only [lookup.go, ih ht, Heap.classPayload?, heap_get_defineMethod_ne hj]
  simpa only [methodOn_eq_go, Proof.ancestors_defineMethod] using go (ancestors h k) hn

theorem RootInitOk.write_outside {D : DefTable} {h : Heap} {cls : ObjId} {name : String} {md : MethodDef}
    (hp : RootInitOk D h) (hn : cls ∉ ancestors h Boot.objectId) :
    RootInitOk D (defineMethod h cls name md) := hp.transport id (methodOn_defineMethod_outside hn)

theorem RootInitOk.defineTop {D : DefTable} {h : Heap} {d : Defn} {md : MethodDef}
    (hp : RootInitOk D h) : RootInitOk (d :: D) (defineMethod h Boot.objectId d.name md) := by
  intro hf
  obtain ⟨hn, hD⟩ := rootInitFreeB_cons hf
  simpa only [Interp.userInit?, methodOn_defineMethod h Boot.objectId Boot.objectId d.name "initialize" md hn.symm]
    using hp hD

#print axioms RootInitOk.write_outside
#print axioms RootInitOk.defineTop
end Ratchet.Denote
