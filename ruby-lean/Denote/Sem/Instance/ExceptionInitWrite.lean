import Denote.Sem.Names.OwnLookup

/-! Exception initialization is resolved before Object. Program method writes
preserve the protected native prefix, including a top-level initialize definition. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem methodOn_init_shape {h : Heap} (hc : Proof.ChainsIn h)
    (hs : primitiveInitShapeB h = true) :
    Interp.methodOn h Boot.zeroDivisionErrorId "initialize" =
      (errorInitOwn h Boot.exceptionId).map (Boot.exceptionId, ·) := by
  simp only [primitiveInitShapeB, Bool.and_eq_true, beq_iff_eq,
    Option.isNone_iff_eq_none] at hs
  obtain ⟨⟨⟨hchain, hz⟩, hstd⟩, hexc⟩ := hs
  rw [methodOn_eq_scan hc, hchain]
  change Proof.lookupScan h "initialize"
    ([Boot.zeroDivisionErrorId, Boot.standardErrorId] ++
      [Boot.exceptionId, Boot.objectId, Boot.kernelId, Boot.basicObjectId]) = _
  rw [lookup_go_skip (by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact hz
    · exact hstd)]
  cases hp : h.classPayload? Boot.exceptionId with
  | none => simp [errorInitOwn, hp] at hexc
  | some cp =>
    cases hf : cp.methods.find? (·.1 == "initialize") with
    | none => simp [errorInitOwn, hp, hf] at hexc
    | some p =>
      have hv : p.2.visibilityOnly = false := by
        simpa [errorInitOwn, hp, hf] using hexc
      simp only [Proof.lookupScan, hp, hf, hv, Bool.not_false, ↓reduceIte,
        errorInitOwn, Option.bind_some, Option.map_some]

theorem primitiveInitB_defineMethod_outside {h : Heap} {cls : ObjId} {name : String} {md : MethodDef}
    (hi : primitiveInitB h = true) (hc : Proof.ChainsIn h)
    (hz : Boot.zeroDivisionErrorId ≠ cls) (hs : Boot.standardErrorId ≠ cls)
    (he : Boot.exceptionId ≠ cls) : primitiveInitB (defineMethod h cls name md) = true := by
  have hshape : primitiveInitShapeB h = true := by
    have hh := hi
    simp only [primitiveInitB, Bool.and_eq_true] at hh
    exact hh.1
  have own (k : ObjId) (hk : k ≠ cls) :
      errorInitOwn (defineMethod h cls name md) k = errorInitOwn h k := by
    simp only [errorInitOwn, Heap.classPayload?, heap_get_defineMethod_ne hk]
  have hnshape : primitiveInitShapeB (defineMethod h cls name md) = true := by
    simpa only [primitiveInitShapeB, Proof.ancestors_defineMethod, own _ hz, own _ hs, own _ he]
      using hshape
  have hmethod : Interp.methodOn (defineMethod h cls name md) Boot.zeroDivisionErrorId "initialize" =
      Interp.methodOn h Boot.zeroDivisionErrorId "initialize" := by
    rw [methodOn_init_shape (Proof.chainsIn_defineMethod hc) hnshape,
      methodOn_init_shape hc hshape, own _ he]
  simpa only [primitiveInitB, hnshape, primitiveInitClasses, List.all_cons, List.all_nil,
    hmethod, Proof.ancestors_defineMethod, crubyShadow_defineMethod, Bool.and_true,
    Bool.true_and, hshape] using hi

theorem primitiveInitB_defineMethod_other {h : Heap} {cls : ObjId} {name : String} {md : MethodDef}
    (hi : primitiveInitB h = true) (hn : "initialize" ≠ name) :
    primitiveInitB (defineMethod h cls name md) = true := by
  have own (k : ObjId) : errorInitOwn (defineMethod h cls name md) k = errorInitOwn h k := by
    have hh := Proof.methods_find_defineMethod h cls k name "initialize" md hn
    cases hp : (defineMethod h cls name md).classPayload? k <;>
      cases hq : h.classPayload? k <;> simp_all [errorInitOwn]
  simpa only [primitiveInitB, primitiveInitShapeB, own, Proof.ancestors_defineMethod,
    methodOn_defineMethod h cls _ name "initialize" md hn, crubyShadow_defineMethod] using hi

#print axioms primitiveInitB_defineMethod_outside
#print axioms primitiveInitB_defineMethod_other
end Ratchet.Denote
