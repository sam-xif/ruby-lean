import Denote.Sem.Subclass.SubclassDispatch

/-! Query and primitive-dispatch conformance for arbitrary fresh subclasses. Each new
lookup site is mapped to its old source; native metadata is checked independently. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet RubyCore.Proof

def FreshClass.NativeQuiet (name mn : String) : Prop :=
  crubyClassDefines name mn = false ∧ crubyClassDefines ("#<Class:" ++ name ++ ">") mn = false

namespace Subclass
variable {h : Heap} {d parent eParent : ObjId} {name q : String}
local notation "h₁" => heap h d name q parent eParent

theorem class_site_source (hc : ChainsIn h) (hp : (h.classPayload? parent).isSome = true)
    (he : (h.get parent).eigen = some eParent) {k : ObjId} (hk : ClassQuerySite h₁ k) :
    ClassQuerySite h (source h parent eParent k) := by
  rcases hk with hk | ⟨o, hp', hco⟩
  · subst k; rw [source_old hc.boot.1]; exact Or.inl rfl
  · subst k
    by_cases hl : o < h.objs.size
    · have hp₀ : (h.classPayload? o).isSome = true := by rwa [classPayload_old_isSome hl] at hp'
      rw [classOf_old hl, source_old (ClsGrow.classOf_lt hc hl)]
      exact Or.inr ⟨o, hp₀, rfl⟩
    · by_cases hok : o = h.objs.size
      · subst o
        rw [classOf_class]
        simp only [source, if_neg (Nat.succ_ne_self _), ite_true]
        exact Or.inr ⟨parent, hp, by simp only [classOf, he]⟩
      · by_cases hoe : o = h.objs.size + 1
        · subst o
          rw [classOf_eigen, source_old hc.boot.1]
          exact Or.inl rfl
        · rw [cp_oob (Nat.le_of_not_lt (Judgment.not_lt_add_two hl hok hoe))] at hp'
          contradiction

theorem primitiveDispatch (hc : ChainsIn h) (hs : Saturated h) (free : String → Bool) :
    primitiveDispatchB h₁ free = primitiveDispatchB h free := by
  apply Bool.eq_iff_iff.mpr
  simp only [primitiveDispatchB, List.all_eq_true]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro hp
  rcases p with ⟨k, mn, bid⟩
  have hbound : k ≤ Boot.procId := of_decide_eq_true (List.all_eq_true.mp
    (by decide : primitiveMethods.all (fun p => decide (p.1 ≤ Boot.procId)) = true) _ hp)
  have hk := Nat.lt_of_le_of_lt hbound hc.boot.2.2.2.1
  simp only [method_old hc hs hk, shadow_before_old hc hs hk]

theorem primitiveErrors (hc : ChainsIn h) (hs : Saturated h) : primitiveErrorsB h₁ = primitiveErrorsB h := by
  apply Bool.eq_iff_iff.mpr
  simp only [primitiveErrorsB, List.all_eq_true]
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro hk
  have hl : k < h.objs.size := by
    have hb : k ≤ Boot.procId := of_decide_eq_true (List.all_eq_true.mp
      (by decide : primitiveErrorClasses.all (fun j => decide (j ≤ Boot.procId)) = true) _ hk)
    exact Nat.lt_of_le_of_lt hb hc.boot.2.2.2.1
  simp only [primitiveErrorB, ancestors_old hc hs hl]

variable {κ : Ctx} {m n : Machine}

theorem query (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hp : parent < m.heap.objs.size) (he : eParent < m.heap.objs.size) (hne : q.isEmpty = false)
    (hn : ∀ mn bid, (mn, bid) ∈ queryBuiltins → nameFreeN κ mn = true → FreshClass.NativeQuiet q mn)
    (hh : n.heap = heap m.heap d name q parent eParent) (hq : QueryOk κ m) : QueryOk κ n := by
  intro mn bid hmem hfree k
  obtain ⟨hFound, hMiss⟩ := hq mn bid hmem hfree (source m.heap parent eParent k)
  obtain ⟨hn₁, hn₂⟩ := hn mn bid hmem hfree
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_source hc hs hp he] at hf
    obtain ⟨hb, hu, hv, hp', hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp', ?_⟩
    rw [hh]
    exact shadow_before_source hc hs hp he hne hn₁ hn₂ k owner hsh
  · intro hm owner md hf
    rw [hh, method_source hc hs hp he] at hm hf
    exact hMiss hm owner md hf

theorem clsQuery (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hp : (m.heap.classPayload? parent).isSome = true) (he : (m.heap.get parent).eigen = some eParent)
    (hne : q.isEmpty = false)
    (hn : ∀ mn bid, (mn, bid) ∈ clsQueryBuiltins → nameFreeN κ mn = true → FreshClass.NativeQuiet q mn)
    (hh : n.heap = heap m.heap d name q parent eParent) (hq : ClsQueryOk κ m) : ClsQueryOk κ n := by
  intro mn bid hmem hfree k hk
  rw [hh] at hk
  have hpl := lt_size_of_classPayload hp
  have hel := hc.eigen parent hpl eParent he
  obtain ⟨hFound, hMiss⟩ := hq mn bid hmem hfree (source m.heap parent eParent k) (class_site_source hc hp he hk)
  obtain ⟨hn₁, hn₂⟩ := hn mn bid hmem hfree
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_source hc hs hpl hel] at hf
    obtain ⟨hb, hu, hv, hp', hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp', ?_⟩
    rw [hh]
    exact shadow_before_source hc hs hpl hel hne hn₁ hn₂ k owner hsh
  · intro hm owner md hf
    rw [hh, method_source hc hs hpl hel] at hm hf
    exact hMiss hm owner md hf

theorem nilQuery (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hp : parent < m.heap.objs.size) (he : eParent < m.heap.objs.size) (hne : q.isEmpty = false)
    (hn : nameFreeN κ "nil?" = true → FreshClass.NativeQuiet q "nil?")
    (hh : n.heap = heap m.heap d name q parent eParent) (hq : NilQueryOk κ m) : NilQueryOk κ n := by
  intro hfree k
  obtain ⟨hFound, hMiss⟩ := hq hfree (source m.heap parent eParent k)
  obtain ⟨hn₁, hn₂⟩ := hn hfree
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_source hc hs hp he] at hf
    obtain ⟨hb, hu, hv, hp', hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp', ?_⟩
    rw [hh]
    exact shadow_before_source hc hs hp he hne hn₁ hn₂ k owner hsh
  · intro hm owner md hf
    rw [hh, method_source hc hs hp he] at hm hf
    exact hMiss hm owner md hf

#print axioms primitiveDispatch
#print axioms primitiveErrors
#print axioms query
#print axioms clsQuery
#print axioms nilQuery
end Subclass
end Ratchet.Denote
