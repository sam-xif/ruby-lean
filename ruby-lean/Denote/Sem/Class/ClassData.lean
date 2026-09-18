import Denote.Sem.Core.DataPres
import Denote.Ty.Ext
import RubyCore.Proof.ClsCongr

/-! First-order preservation for class-allocating heaps. Producers prove old observations
and fresh BasicObject membership; arrays, hashes and exact-instance fields share this proof. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem dataPres_of_class_growth {h h' : Heap} (hc : Proof.ChainsIn h)
    (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (hz : h.objs.size ≤ h'.objs.size)
    (hf : ∀ o, o < h.objs.size → (h'.get o).ivars = (h.get o).ivars ∧
      (h'.get o).klass = (h.get o).klass ∧ (h'.get o).eigen = (h.get o).eigen)
    (hg : ∀ o, o < h.objs.size → h.classPayload? o = none → h'.get o = h.get o)
    (ha : ∀ k, k < h.objs.size → ancestors h' k = ancestors h k)
    (hr : ∀ o, h.objs.size ≤ o → isA h' (.ref o) Boot.basicObjectId = true)
    (hn : ∀ cn k, classNamed? h cn = some k → classNamed? h' cn = some k) : DataPres h h' := by
  have hbound {v : Value} {k : ObjId} (hl : classOf h v < h.objs.size)
      (he : classOf h' v = classOf h v) (hv : isA h v k = true) : isA h' v k = true := by
    rw [isA, he, ha _ hl]; exact hv
  have hisA {v : Value} {k : ObjId} (hv : isA h v k = true) : isA h' v k = true := by
    cases v with
    | ref o =>
      by_cases ho : o < h.objs.size
      · exact hbound (Proof.ClsGrow.classOf_lt hc ho)
          (by simp only [classOf, (hf o ho).2.1, (hf o ho).2.2]) hv
      · have hl := Nat.le_of_not_lt ho
        have hk : k = Boot.basicObjectId := by
          simpa only [isA, classOf_oob h hl, hb, List.contains_cons, List.contains_nil,
            Bool.or_false, beq_iff_eq] using hv
        subst k
        exact hr o hl
    | bool b =>
      cases b <;> exact hbound
        (Nat.lt_of_le_of_lt (by simp only [classOf]; decide) hc.boot.2.2.2.1) rfl hv
    | _ =>
      exact hbound
        (Nat.lt_of_le_of_lt (by simp only [classOf]; decide) hc.boot.2.2.2.1) rfl hv
  refine ⟨?_, hn, ?_, ?_, ?_⟩
  · intro v cn hv
    unfold isAName at hv ⊢
    cases hk : classNamed? h cn with
    | none => rw [hk] at hv; cases hv
    | some k => rw [hn cn k hk]; rw [hk] at hv; exact hisA hv
  · intro v cn hv
    unfold isExactInst at hv ⊢
    cases hk : classNamed? h cn with
    | none => rw [hk] at hv; cases v <;> simp_all
    | some k =>
      rw [hk] at hv
      rw [hn cn k hk]
      cases v with
      | ref o =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv ⊢
        obtain ⟨⟨hl, he⟩, hkl⟩ := hv
        refine ⟨⟨⟨Nat.lt_of_lt_of_le hl hz, ?_⟩, ?_⟩, ?_⟩
        · rw [(hf o hl).2.2]; exact he
        · rw [(hf o hl).2.1]; exact hkl
        · funext x; simp only [ivarOf, (hf o hl).1]
      | _ => simp_all
  · intro v xs hv
    cases v with
    | ref o =>
      have hp : h.classPayload? o = none := by
        unfold Heap.classPayload?
        cases he : (h.get o).payload <;> simp_all [arrElems?]
      rw [arrElems?, hg o (lt_of_arrElems? hv) hp]; exact hv
    | _ => exact absurd hv (by simp [arrElems?])
  · intro v es hv
    cases v with
    | ref o =>
      have hp : h.classPayload? o = none := by
        unfold Heap.classPayload?
        cases he : (h.get o).payload <;> simp_all [hshEntries?]
      rw [hshEntries?, hg o (lt_of_hshEntries? hv) hp]; exact hv
    | _ => exact absurd hv (by simp [hshEntries?])

#print axioms dataPres_of_class_growth
end Ratchet.Denote
