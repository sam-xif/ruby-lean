import Denote.Sem.Module.ModuleDispatchActual
import Denote.Sem.Class.ClassQueriesActual

/-! Query transfers at the actual module heap. The module's own (empty) lookup makes
both obligations vacuous there; every other id reuses its old source site. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModuleActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment
variable {m : Machine} {name : String}
local notation "h₁" => heap m name

theorem classOf_module (hd : m.lexicalNamespace < m.heap.objs.size) :
    classOf h₁ (.ref m.heap.objs.size) = m.heap.objs.size + 1 := by
  simp only [classOf, get_module hd]

theorem classOf_eigen : classOf h₁ (.ref (m.heap.objs.size + 1)) = Boot.classId := by
  simp only [classOf, get_eigen, attachedModuleEigen]

theorem class_site_source (hc : ChainsIn m.heap) (hd : m.lexicalNamespace < m.heap.objs.size)
    {k : ObjId} (hk : ClassQuerySite h₁ k) : ClassQuerySite m.heap (source m.heap k) := by
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
        rw [classOf_module hd]
        simp only [source, ite_true]
        exact Or.inr (Or.inl rfl)
      · by_cases hoe : o = m.heap.objs.size + 1
        · subst o
          rw [classOf_eigen, source_old hc.boot.1]
          exact Or.inl rfl
        · rw [classPayload?_oob _ _ (by rw [size m name]; exact Judgment.not_lt_add_two hl hok hoe)] at hp'
          contradiction

/-- The module object itself is nobody's dispatch class. -/
theorem site_ne_module (hc : ChainsIn m.heap) (hd : m.lexicalNamespace < m.heap.objs.size)
    {k : ObjId} (hk : ClassQuerySite h₁ k) : k ≠ m.heap.objs.size := by
  rcases hk with hk | hk | ⟨o, hp', hco⟩
  · subst k; exact Nat.ne_of_lt hc.boot.1
  · subst k; exact Nat.ne_of_lt hc.boot.2.1
  · subst k
    by_cases hl : o < m.heap.objs.size
    · rw [classOf_old hd hl]; exact Nat.ne_of_lt (ClsGrow.classOf_lt hc hl)
    · by_cases hok : o = m.heap.objs.size
      · subst o; rw [classOf_module hd]; exact Nat.succ_ne_self _
      · by_cases hoe : o = m.heap.objs.size + 1
        · subst o; rw [classOf_eigen]; exact Nat.ne_of_lt hc.boot.1
        · rw [classPayload?_oob _ _ (by rw [size m name]; exact Judgment.not_lt_add_two hl hok hoe)] at hp'
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
    (hne : name.isEmpty = false)
    (hn : ∀ mn bid, (mn, bid) ∈ queryBuiltins → nameFreeN κ mn = true → FreshClass.NativeQuiet name mn)
    (hh : n.heap = h₁) (hq : QueryOk κ m) : QueryOk κ n := by
  intro mn bid hmem hfree k
  by_cases hk : k = m.heap.objs.size
  · subst k
    refine ⟨fun owner md hf => ?_, fun _ owner md hf => ?_⟩ <;>
      (rw [hh, method_module hc hd] at hf; cases hf)
  obtain ⟨hFound, hMiss⟩ := hq mn bid hmem hfree (source m.heap k)
  obtain ⟨_, hn₂⟩ := hn mn bid hmem hfree
  have hn₃ : crubySingletonDefines name mn = false := FreshClassActual.singleton_query_free (by
    have hm : mn ∈ queryBuiltins.map (·.1) := List.mem_map.mpr ⟨(mn, bid), hmem, rfl⟩
    simp only [queryBuiltins, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp)
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_source hc hs hd hk] at hf
    obtain ⟨hb, hu, hv, hp', hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp', ?_⟩
    rw [hh]
    exact shadow_before_source hnames hc hs hd hne hn₂ hn₃ hlmain hk owner hsh
  · intro hm owner md hf
    rw [hh, method_source hc hs hd hk] at hm hf
    exact hMiss hm owner md hf

theorem clsQuery (hnames : NamesOk m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hlmain : Boot.mainId < m.heap.objs.size)
    (hne : name.isEmpty = false)
    (hn : ∀ mn bid, (mn, bid) ∈ clsQueryBuiltins → nameFreeN κ mn = true → FreshClass.NativeQuiet name mn)
    (hh : n.heap = h₁) (hq : ClsQueryOk κ m) : ClsQueryOk κ n := by
  intro mn bid hmem hfree k hsite
  rw [hh] at hsite
  by_cases hk : k = m.heap.objs.size
  · exact absurd hk (site_ne_module hc hd hsite)
  obtain ⟨hFound, hMiss⟩ := hq mn bid hmem hfree (source m.heap k) (class_site_source hc hd hsite)
  obtain ⟨_, hn₂⟩ := hn mn bid hmem hfree
  have hn₃ : crubySingletonDefines name mn = false := FreshClassActual.singleton_query_free (by
    have hm : mn ∈ clsQueryBuiltins.map (·.1) := List.mem_map.mpr ⟨(mn, bid), hmem, rfl⟩
    simp only [clsQueryBuiltins, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp)
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_source hc hs hd hk] at hf
    obtain ⟨hb, hu, hv, hp', hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp', ?_⟩
    rw [hh]
    exact shadow_before_source hnames hc hs hd hne hn₂ hn₃ hlmain hk owner hsh
  · rw [hh, method_source hc hs hd hk]; exact hMiss

theorem nilQuery (hnames : NamesOk m.heap) (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hlmain : Boot.mainId < m.heap.objs.size)
    (hne : name.isEmpty = false)
    (hn : nameFreeN κ "nil?" = true → FreshClass.NativeQuiet name "nil?")
    (hh : n.heap = h₁) (hq : NilQueryOk κ m) : NilQueryOk κ n := by
  intro hfree k
  by_cases hk : k = m.heap.objs.size
  · subst k
    refine ⟨fun owner md hf => ?_, fun _ owner md hf => ?_⟩ <;>
      (rw [hh, method_module hc hd] at hf; cases hf)
  obtain ⟨hFound, hMiss⟩ := hq hfree (source m.heap k)
  obtain ⟨_, hn₂⟩ := hn hfree
  have hn₃ : crubySingletonDefines name "nil?" = false := FreshClassActual.singleton_query_free (by simp)
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_source hc hs hd hk] at hf
    obtain ⟨hb, hu, hv, hp', hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp', ?_⟩
    rw [hh]
    exact shadow_before_source hnames hc hs hd hne hn₂ hn₃ hlmain hk owner hsh
  · intro hm owner md hf
    rw [hh, method_source hc hs hd hk] at hm hf
    exact hMiss hm owner md hf

#print axioms query
#print axioms clsQuery
#print axioms nilQuery
end Ratchet.Denote.FreshModuleActual
