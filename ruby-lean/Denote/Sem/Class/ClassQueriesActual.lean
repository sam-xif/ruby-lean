import Denote.Sem.Class.ClassDispatchActual
import Denote.Sem.Subclass.SubclassQueries

/-! Reuse the original query transfer with actual source sites and native shadows. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment
variable {p : ObjId}
variable {m : Machine} {name : String} {e : ObjId}
local notation "h₁" => heap m name e p

private theorem singleton_query_rows : crubySingletonNames.all (fun p =>
    ["is_a?", "class", "raise", "===", "to_s", "nil?"].all (fun mn => !p.2.contains mn)) = true := by decide

/-- None of the existing query selectors is a CRuby singleton-name blocker. -/
theorem singleton_query_free {cn mn : String}
    (hm : mn ∈ ["is_a?", "class", "raise", "===", "to_s", "nil?"]) :
    crubySingletonDefines cn mn = false := by
  unfold crubySingletonDefines
  cases hf : crubySingletonNames.find? (·.1 == cn) with
  | none => rfl
  | some p =>
    have hp := List.all_eq_true.mp (List.all_eq_true.mp singleton_query_rows p
      (List.mem_of_find?_eq_some hf)) mn hm
    simpa only [Bool.not_eq_true'] using hp

theorem classOf_class (hd : m.lexicalNamespace < m.heap.objs.size) :
    classOf h₁ (.ref m.heap.objs.size) = m.heap.objs.size + 1 := by
  simp only [classOf, get_class hd]

theorem classOf_eigen :
    classOf h₁ (.ref (m.heap.objs.size + 1)) = Boot.classId := by
  simp only [classOf, get_eigen, attachedClassEigen]

theorem class_site_source (hc : ChainsIn m.heap) (hd : m.lexicalNamespace < m.heap.objs.size) (hp : (m.heap.classPayload? p).isSome = true)
    (he : (m.heap.get p).eigen = some e) {k : ObjId} (hk : ClassQuerySite h₁ k) :
    ClassQuerySite m.heap (source m.heap e k p) := by
  rcases hk with hk | hk | ⟨o, hp', hco⟩
  · subst k; rw [source_old hc.boot.1]; exact Or.inl rfl
  · subst k; rw [source_old hc.boot.2.1]; exact Or.inr (Or.inl rfl)
  · subst k
    by_cases hl : o < m.heap.objs.size
    · have hp₀ : (m.heap.classPayload? o).isSome = true := by rwa [classPayload_live hd hl] at hp'
      rw [classOf_old hd hl, source_old (ClsGrow.classOf_lt hc hl)]
      exact Or.inr (Or.inr ⟨o, hp₀, rfl⟩)
    · by_cases hok : o = m.heap.objs.size
      · subst o
        rw [classOf_class hd]
        simp only [source, Subclass.source, if_neg (Nat.succ_ne_self _), ite_true]
        exact Or.inr (Or.inr ⟨p, hp, by simp only [classOf, he]⟩)
      · by_cases hoe : o = m.heap.objs.size + 1
        · subst o
          rw [classOf_eigen, source_old hc.boot.1]
          exact Or.inl rfl
        · rw [classPayload?_oob _ _ (by rw [size m name e]; exact Judgment.not_lt_add_two hl hok hoe)] at hp'
          contradiction

theorem primitiveDispatch (hnames : NamesOk m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (free : String → Bool) :
    primitiveDispatchB h₁ free = primitiveDispatchB m.heap free := by
  change (nativeDispatchB h₁ free && eachDispatchB h₁ free) =
    (nativeDispatchB m.heap free && eachDispatchB m.heap free)
  refine congr (congrArg Bool.and ?_) ?_
  · apply Bool.eq_iff_iff.mpr
    simp only [nativeDispatchB, List.all_eq_true]
    apply forall_congr'
    intro p
    apply imp_congr_right
    intro hp
    rcases p with ⟨k, mn, bid⟩
    have hbound : k ≤ Boot.procId := of_decide_eq_true (List.all_eq_true.mp
      (by decide : dispatchMethods.all (fun p => decide (p.1 ≤ Boot.procId)) = true) _ hp)
    have hk := Nat.lt_of_le_of_lt hbound hc.boot.2.2.2.1
    simp only [method_old hc hs hd hk, shadow_before_old hnames hc hs hd hk]
  · have hk : Boot.arrayId < m.heap.objs.size :=
      Nat.lt_of_le_of_lt (by decide : Boot.arrayId ≤ Boot.procId) hc.boot.2.2.2.1
    simp only [eachDispatchB, method_old hc hs hd hk, shadow_before_old hnames hc hs hd hk]

theorem primitiveErrors (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) : primitiveErrorsB h₁ = primitiveErrorsB m.heap := by
  apply Bool.eq_iff_iff.mpr
  simp only [primitiveErrorsB, List.all_eq_true]
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro hk
  have hl : k < m.heap.objs.size := by
    have hb : k ≤ Boot.procId := of_decide_eq_true (List.all_eq_true.mp
      (by decide : primitiveErrorClasses.all (fun j => decide (j ≤ Boot.procId)) = true) _ hk)
    exact Nat.lt_of_le_of_lt hb hc.boot.2.2.2.1
  simp only [primitiveErrorB, ancestors_old hc hs hd hl]

variable {κ : Ctx} {n : Machine}

theorem query (hnames : NamesOk m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hlmain : Boot.mainId < m.heap.objs.size)
    (he : e < m.heap.objs.size) (hpl : p < m.heap.objs.size) (hne : name.isEmpty = false)
    (hn : ∀ mn bid, (mn, bid) ∈ queryBuiltins → nameFreeN κ mn = true → FreshClass.NativeQuiet name mn)
    (hh : n.heap = heap m name e p) (hq : QueryOk κ m) : QueryOk κ n := by
  intro mn bid hmem hfree k
  obtain ⟨hFound, hMiss⟩ := hq mn bid hmem hfree (source m.heap e k p)
  obtain ⟨hn₁, hn₂⟩ := hn mn bid hmem hfree
  have hn₃ : crubySingletonDefines name mn = false := singleton_query_free (by
    have hm : mn ∈ queryBuiltins.map (·.1) := List.mem_map.mpr ⟨(mn, bid), hmem, rfl⟩
    simp only [queryBuiltins, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp)
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_source hc hs hd he hpl] at hf
    obtain ⟨hb, hu, hv, hp', hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp', ?_⟩
    rw [hh]
    exact shadow_before_source hnames hc hs hd he hne hn₁ hn₂ hn₃ hlmain hpl k owner hsh
  · intro hm owner md hf
    rw [hh, method_source hc hs hd he hpl] at hm hf
    exact hMiss hm owner md hf

theorem clsQuery (hnames : NamesOk m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hlmain : Boot.mainId < m.heap.objs.size)
    (hp : (m.heap.classPayload? p).isSome = true) (he : (m.heap.get p).eigen = some e)
    (hne : name.isEmpty = false)
    (hn : ∀ mn bid, (mn, bid) ∈ clsQueryBuiltins → nameFreeN κ mn = true → FreshClass.NativeQuiet name mn)
    (hh : n.heap = heap m name e p) (hq : ClsQueryOk κ m) : ClsQueryOk κ n := by
  intro mn bid hmem hfree k hk
  rw [hh] at hk
  have hpl := lt_size_of_classPayload hp
  have hel := hc.eigen p hpl e he
  obtain ⟨hFound, hMiss⟩ := hq mn bid hmem hfree (source m.heap e k p) (class_site_source hc hd hp he hk)
  obtain ⟨hn₁, hn₂⟩ := hn mn bid hmem hfree
  have hn₃ : crubySingletonDefines name mn = false := singleton_query_free (by
    have hm : mn ∈ clsQueryBuiltins.map (·.1) := List.mem_map.mpr ⟨(mn, bid), hmem, rfl⟩
    simp only [clsQueryBuiltins, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp)
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_source hc hs hd hel hpl] at hf
    obtain ⟨hb, hu, hv, hp', hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp', ?_⟩
    rw [hh]
    exact shadow_before_source hnames hc hs hd hel hne hn₁ hn₂ hn₃ hlmain hpl k owner hsh
  · intro hm owner md hf
    rw [hh, method_source hc hs hd hel hpl] at hm hf
    exact hMiss hm owner md hf

theorem nilQuery (hnames : NamesOk m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hlmain : Boot.mainId < m.heap.objs.size)
    (he : e < m.heap.objs.size) (hpl : p < m.heap.objs.size) (hne : name.isEmpty = false)
    (hn : nameFreeN κ "nil?" = true → FreshClass.NativeQuiet name "nil?")
    (hh : n.heap = heap m name e p) (hq : NilQueryOk κ m) : NilQueryOk κ n := by
  intro hfree k
  obtain ⟨hFound, hMiss⟩ := hq hfree (source m.heap e k p)
  obtain ⟨hn₁, hn₂⟩ := hn hfree
  have hn₃ : crubySingletonDefines name "nil?" = false := singleton_query_free (by simp)
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_source hc hs hd he hpl] at hf
    obtain ⟨hb, hu, hv, hp', hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp', ?_⟩
    rw [hh]
    exact shadow_before_source hnames hc hs hd he hne hn₁ hn₂ hn₃ hlmain hpl k owner hsh
  · intro hm owner md hf
    rw [hh, method_source hc hs hd he hpl] at hm hf
    exact hMiss hm owner md hf

#print axioms primitiveDispatch
#print axioms primitiveErrors
#print axioms query
#print axioms clsQuery
#print axioms nilQuery
end Ratchet.Denote.FreshClassActual
