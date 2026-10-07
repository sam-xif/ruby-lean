import Books.Metatheory.Heap.HeapFacts

/-! Metadata checked by ordinary class construction and inherited at class creation. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore

def allocationReadyB (cp : ClassPayload) : Bool :=
  !cp.attached.isSome && cp.initialized && cp.ancestryReady && !cp.allocatorUnavailable

def plainAllocationReadyB (h : Heap) (k : ObjId) : Bool :=
  (h.classPayload? k).any allocationReadyB

/-- Inheritable flags of a superclass (Object by default). -/
def objectClassFlagsB (h : Heap) (p : ObjId := Boot.objectId) : Bool :=
  (h.classPayload? p).any fun cp => cp.ancestryReady && !cp.allocatorUnavailable

theorem classPayload_metadata_defineMethod {h : Heap} {cls k : ObjId}
    {name : String} {md : MethodDef} (f : ClassPayload → Bool)
    (hf : ∀ cp, f { cp with methods := (name, md) :: cp.methods.filter (·.1 != name) } = f cp) :
    ((defineMethod h cls name md).classPayload? k).any f = (h.classPayload? k).any f := by
  unfold defineMethod
  split
  · rename_i cp hc
    by_cases hk : k = cls
    · subst k
      have hl : cls < h.objs.size := by
        by_cases hn : cls < h.objs.size
        · exact hn
        · rw [Proof.classPayload?_oob h cls hn] at hc
          cases hc
      simp only [Heap.setClassPayload, Heap.classPayload?, Heap.get, Heap.set,
        Proof.objs_getD_set!_self _ _ _ hl]
      change f { cp with methods := (name, md) :: cp.methods.filter (·.1 != name) } =
        (h.classPayload? cls).any f
      rw [hf, hc]
      rfl
    · simp only [Heap.setClassPayload, Heap.classPayload?, Heap.get, Heap.set]
      rw [Proof.objs_getD_set!_ne _ _ _ _ hk]
  · rfl

theorem plainAllocationReadyB_defineMethod (h : Heap) (cls k : ObjId)
    (name : String) (md : MethodDef) :
    plainAllocationReadyB (defineMethod h cls name md) k = plainAllocationReadyB h k :=
  classPayload_metadata_defineMethod allocationReadyB (fun _ => rfl)

theorem objectClassFlagsB_defineMethod (h : Heap) (cls : ObjId)
    (name : String) (md : MethodDef) :
    objectClassFlagsB (defineMethod h cls name md) = objectClassFlagsB h :=
  classPayload_metadata_defineMethod (fun cp => cp.ancestryReady && !cp.allocatorUnavailable)
    (fun _ => rfl)

#print axioms plainAllocationReadyB_defineMethod
#print axioms objectClassFlagsB_defineMethod
end Checker.Soundness
