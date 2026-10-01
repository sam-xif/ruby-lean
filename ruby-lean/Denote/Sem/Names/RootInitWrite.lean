import Denote.Sem.Instance.MethodHeap

/-! Root initialization is preserved by writes outside its physical chain. A top-level
definition updates the existing def table; only initialize itself waives root absence. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem methodOn_defineMethod_outside {h : Heap} {cls k : ObjId} {name query : String} {md : MethodDef}
    (hn : cls ∉ ancestors h k) (hb : cls ∉ ancestors h Boot.objectId) :
    Interp.methodOn (defineMethod h cls name md) k query = Interp.methodOn h k query := by
  have go : ∀ fuel (ks : List ObjId) used, cls ∉ ks →
      lookupInChain.go (defineMethod h cls name md) query fuel ks used =
        lookupInChain.go h query fuel ks used := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro ks used hn
      cases ks with
      | nil => rfl
      | cons j js =>
        have hj : j ≠ cls := fun he => hn (he ▸ List.mem_cons_self)
        have ht : cls ∉ js := fun hm => hn (List.mem_cons_of_mem j hm)
        simp only [lookupInChain.go, Heap.classPayload?, heap_get_defineMethod_ne hj,
          ih js used ht, Proof.ancestors_defineMethod, ih _ true hb]
  simpa only [methodOn_eq_go, lookupInChain, Proof.objs_size_defineMethod,
    Proof.ancestors_defineMethod] using go (2 * h.objs.size + 2) (ancestors h k) false hn

theorem RootInitOk.write_outside {D : DefTable} {h : Heap} {cls : ObjId} {name : String} {md : MethodDef}
    (hp : RootInitOk D h) (hn : cls ∉ ancestors h Boot.objectId) :
    RootInitOk D (defineMethod h cls name md) := hp.transport id (methodOn_defineMethod_outside hn hn)

theorem RootInitOk.defineTop {D : DefTable} {h : Heap} {d : Defn} {md : MethodDef}
    (hp : RootInitOk D h) : RootInitOk (d :: D) (defineMethod h Boot.objectId d.name md) := by
  intro hf
  obtain ⟨hn, hD⟩ := rootInitFreeB_cons hf
  simpa only [initDispatchB, methodOn_defineMethod h Boot.objectId Boot.objectId d.name "initialize" md hn.symm]
    using hp hD

#print axioms RootInitOk.write_outside
#print axioms RootInitOk.defineTop
end Ratchet.Denote
