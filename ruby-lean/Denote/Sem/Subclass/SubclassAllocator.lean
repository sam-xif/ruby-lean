import Denote.Sem.Subclass.SubclassDeclared
import Denote.Sem.Class.ClassShape

/-! A subclass of a plain allocator is itself plain. This says nothing about the
inherited initializer's arity, annotations or body; those remain call obligations. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet

theorem plain {h : Heap} {d parent eParent : ObjId} {name q : String}
    (hc : CoreOk h) (hs : Proof.Saturated h) (hp : PlainAllocator h parent) :
    PlainAllocator (heap h d name q parent eParent) h.objs.size := by
  have hb := named_live hc.regexpNamed
  have hne (k : ObjId) (hk : k ≤ Boot.regexpId) : h.objs.size ≠ k :=
    (Nat.ne_of_lt (Nat.lt_of_le_of_lt hk hb)).symm
  have hchain := ancestors_class (d := d) (name := name) (q := q) (eParent := eParent)
    hc.classReady.chains hs hp.live
  refine ⟨?_, hne _ (by decide), hne _ (by decide), hne _ (by decide),
    hne _ (by decide), ?_, ?_, ?_, ?_⟩
  · rw [size]; exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  · simp only [Heap.classPayload?, get_class, classObjE, Option.map_some]
  · rw [hchain]; exact List.contains_iff_mem.mpr (List.mem_cons_of_mem _ (List.contains_iff_mem.mp hp.rooted))
  · simpa only [Builtins.allocatableCore, hchain, List.find?_cons,
      beq_eq_false_iff_ne.mpr (hne Boot.stringId (by decide)),
      beq_eq_false_iff_ne.mpr (hne Boot.arrayId (by decide)),
      beq_eq_false_iff_ne.mpr (hne Boot.hashId (by decide)),
      beq_eq_false_iff_ne.mpr (hne Boot.exceptionId (by decide)), Bool.false_or, Bool.false_eq_true, ite_false]
      using hp.noCore
  · rw [hchain, List.any_cons, hp.noPayload, Bool.or_false]
    simp [Builtins.payloadCoreClasses]
    exact ⟨⟨hne _ (by decide), hne _ (by decide), hne _ (by decide), hne _ (by decide),
      hne _ (by decide), hne _ (by decide), hne _ (by decide)⟩, hne _ (by decide)⟩

#print axioms plain
end Ratchet.Denote.Subclass
