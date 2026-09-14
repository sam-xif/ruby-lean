import Denote.Sem.ClassDispatch

/-! Query invariants across fresh class creation. Method lookup alone is insufficient:
native-name shadows and the new class-object receiver sites must also be covered. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

def NativeQuiet (name mn : String) : Prop :=
  crubyClassDefines name mn = false ∧ crubyClassDefines ("#<Class:" ++ name ++ ">") mn = false

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem class_site_parent (hc : Proof.ChainsIn h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (he : (h.get Boot.objectId).eigen = some e) {k : ObjId}
    (hk : ClassQuerySite h₁ k) : ClassQuerySite h (parent h e k) := by
  rcases hk with hk | ⟨o, hp, hco⟩
  · subst k; rw [parent_old hc.boot.1]; exact Or.inl rfl
  · subst k
    by_cases hl : o < h.objs.size
    · have hp₀ : (h.classPayload? o).isSome = true := by
        unfold Heap.classPayload? at hp
        rw [Proof.Judgment.freshClsHeap_get_old hl] at hp
        exact (Proof.classPayload?_isSome_constSetIn h Boot.objectId o name _).symm.trans hp
      rw [classOf_old hl, parent_old (Proof.ClsGrow.classOf_lt hc hl)]
      exact Or.inr ⟨o, hp₀, rfl⟩
    · by_cases hok : o = h.objs.size
      · subst o
        rw [Proof.Judgment.classOf_freshC_k]
        simp only [parent, if_neg (Nat.succ_ne_self _), ite_true]
        exact Or.inr ⟨Boot.objectId, ho, by simp only [classOf, he]⟩
      · by_cases hoe : o = h.objs.size + 1
        · subst o
          rw [Proof.Judgment.classOf_freshC_e, parent_old hc.boot.1]
          exact Or.inl rfl
        · have hout := Nat.le_of_not_lt (Proof.Judgment.not_lt_add_two hl hok hoe)
          rw [Proof.Judgment.freshClsHeap_cp_oob hout] at hp
          contradiction

variable {κ : Ctx} {m n : Machine}

theorem query (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (he : e < m.heap.objs.size) (hne : name.isEmpty = false)
    (hn : ∀ mn bid, (mn, bid) ∈ queryBuiltins → nameFreeN κ mn = true → NativeQuiet name mn)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) (hq : QueryOk κ m) :
    QueryOk κ n := by
  intro mn bid hmem hfree k
  obtain ⟨hFound, hMiss⟩ := hq mn bid hmem hfree (parent m.heap e k)
  obtain ⟨hn₁, hn₂⟩ := hn mn bid hmem hfree
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_parent hc hs he] at hf
    obtain ⟨hb, hu, hv, hp, hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp, ?_⟩
    rw [hh]
    exact shadow_before_parent hc hs he hne hn₁ hn₂ k owner hsh
  · intro hm owner md hf
    rw [hh, method_parent hc hs he] at hm hf
    exact hMiss hm owner md hf

theorem clsQuery (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hne : name.isEmpty = false)
    (hn : ∀ mn bid, (mn, bid) ∈ clsQueryBuiltins → nameFreeN κ mn = true → NativeQuiet name mn)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) (hq : ClsQueryOk κ m) :
    ClsQueryOk κ n := by
  intro mn bid hmem hfree k hk
  rw [hh] at hk
  have helt := hc.eigen Boot.objectId hc.boot.2.2.2.2 e he
  obtain ⟨hFound, hMiss⟩ := hq mn bid hmem hfree (parent m.heap e k) (class_site_parent hc ho he hk)
  obtain ⟨hn₁, hn₂⟩ := hn mn bid hmem hfree
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_parent hc hs helt] at hf
    obtain ⟨hb, hu, hv, hp, hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp, ?_⟩
    rw [hh]
    exact shadow_before_parent hc hs helt hne hn₁ hn₂ k owner hsh
  · intro hm owner md hf
    rw [hh, method_parent hc hs helt] at hm hf
    exact hMiss hm owner md hf

theorem nilQuery (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (he : e < m.heap.objs.size) (hne : name.isEmpty = false)
    (hn : nameFreeN κ "nil?" = true → NativeQuiet name "nil?")
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) (hq : NilQueryOk κ m) :
    NilQueryOk κ n := by
  intro hfree k
  obtain ⟨hFound, hMiss⟩ := hq hfree (parent m.heap e k)
  obtain ⟨hn₁, hn₂⟩ := hn hfree
  refine ⟨?_, ?_⟩
  · intro owner md hf
    rw [hh, method_parent hc hs he] at hf
    obtain ⟨hb, hu, hv, hp, hsh⟩ := hFound owner md hf
    refine ⟨hb, hu, hv, hp, ?_⟩
    rw [hh]
    exact shadow_before_parent hc hs he hne hn₁ hn₂ k owner hsh
  · intro hm owner md hf
    rw [hh, method_parent hc hs he] at hm hf
    exact hMiss hm owner md hf

#print axioms class_site_parent
#print axioms query
#print axioms clsQuery
#print axioms nilQuery
end Ratchet.Denote.FreshClass
