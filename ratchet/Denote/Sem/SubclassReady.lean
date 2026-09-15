import Denote.Sem.ClassGrowth
import Denote.Sem.SubclassChains
import Denote.Sem.ClassReady

/-! Bounded edges and both fuel saturations after actual cached-parent subclass entry.
The class and metaclass parents may be any old ids; their semantic roles are separate. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {d parent eParent : ObjId} {name q : String}
local notation "h₁" => heap h d name q parent eParent

theorem fresh_cases {o : ObjId} (ho : h.objs.size ≤ o) (hl : o < (h₁).objs.size) :
    o = h.objs.size ∨ o = h.objs.size + 1 := by
  have hb : o < h.objs.size + 2 := size ▸ hl
  rcases Nat.eq_or_lt_of_le ho with he | he
  · exact Or.inl he.symm
  · exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ hb) he)

theorem chainsIn (hc : ChainsIn h) (hp : parent < h.objs.size) (he : eParent < h.objs.size) :
    ChainsIn h₁ := by
  apply chainsIn_of_clsGrow (h := hmidOf h d name) grow (chainsIn_hmid hc)
  · intro o ho hl
    rw [hmid_size] at ho
    rcases fresh_cases ho hl with rfl | rfl
    all_goals
      simp only [get_class, get_eigen, classObjE, eigObjC, size]
      exact Nat.lt_of_lt_of_le hc.boot.1 (by omega)
  · intro o ho hl e he'
    rw [hmid_size] at ho
    rcases fresh_cases ho hl with rfl | rfl
    · rw [get_class] at he'
      have heq : h.objs.size + 1 = e := Option.some.inj he'
      subst e
      rw [size]; exact Nat.lt_succ_self _
    · rw [get_eigen] at he'; cases he'
  · intro o cp ho hl hcp
    rw [hmid_size] at ho
    rcases fresh_cases ho hl with rfl | rfl
    · simp only [Heap.classPayload?, get_class, classObjE] at hcp
      cases hcp
      exact ⟨fun s hs => by cases hs; rw [size]; exact Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _),
        fun _ hi => False.elim (List.not_mem_nil hi), fun _ hi => False.elim (List.not_mem_nil hi)⟩
    · simp only [Heap.classPayload?, get_eigen, eigObjC] at hcp
      cases hcp
      exact ⟨fun s hs => by cases hs; rw [size]; exact Nat.lt_of_lt_of_le he (Nat.le_add_right _ _),
        fun _ hi => False.elim (List.not_mem_nil hi), fun _ hi => False.elim (List.not_mem_nil hi)⟩

theorem saturated (hc : ChainsIn h) (hs : Saturated h)
    (hp : parent < h.objs.size) (he : eParent < h.objs.size) : Saturated h₁ := by
  apply saturated_of_clsGrow_heads (h := hmidOf h d name) grow (chainsIn_hmid hc)
    (saturated_hmid hs) (by rw [hmid_size, size]; exact Nat.le_refl _)
  · intro k hk hl f
    rw [hmid_size] at hk
    rcases fresh_cases hk hl with rfl | rfl
    all_goals
      rw [modAncestors.go.eq_def]
      simp [Heap.classPayload?, get_class, get_eigen, classObjE, eigObjC]
  · intro k hk hl
    rw [hmid_size] at hk
    rcases fresh_cases hk hl with rfl | rfl
    · refine ⟨parent, by rwa [hmid_size], ?_⟩
      intro f
      rw [ancestors.go.eq_def]
      simp [Heap.classPayload?, get_class, classObjE]
    · refine ⟨eParent, by rwa [hmid_size], ?_⟩
      intro f
      rw [ancestors.go.eq_def]
      simp [Heap.classPayload?, get_eigen, eigObjC]

#print axioms chainsIn
#print axioms saturated
end Ratchet.Denote.Subclass

namespace Ratchet.Denote
open RubyCore RubyCore.Proof RubyCore.Proof.Judgment

theorem ConstRefsLive.subclass {h : Heap} {d parent eParent : ObjId} {name q : String}
    (hc : ConstRefsLive h) (ho : Boot.objectId < h.objs.size) :
    ConstRefsLive (Subclass.heap h d name q parent eParent) := by
  intro cn k hk
  have hold : constOwn (Subclass.heap h d name q parent eParent) Boot.objectId cn =
      constOwn (hmidOf h d name) Boot.objectId cn := by
    unfold constOwn
    rw [Subclass.grow.payloadOld (by rwa [hmid_size])]
  rw [hold] at hk
  have hk' : k = h.objs.size ∨ k < h.objs.size := by
    by_cases hd : Boot.objectId = d
    · subst d
      by_cases hn : cn = name
      · subst cn
        cases hp : h.classPayload? Boot.objectId with
        | none => simp [hmidOf, constSetIn, constOwn, hp] at hk
        | some cp =>
          rw [constOwn_constSetIn_self (by simp [hp]) ho] at hk
          exact Or.inl (Value.ref.inj (Option.some.inj hk)).symm
      · rw [constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inr hn)] at hk
        exact Or.inr (hc cn k hk)
    · rw [constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inl hd)] at hk
      exact Or.inr (hc cn k hk)
  rw [Subclass.size]
  rcases hk' with rfl | hk'
  · exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  · exact Nat.lt_of_lt_of_le hk' (Nat.le_add_right _ _)

/-- Preserve the existing readiness contract, including Object's independent cached
metaclass and its separation from builtin bases. No new class-specific state flag. -/
theorem ClassReady.subclass {h : Heap} {d parent eParent : ObjId} {name q : String}
    (hc : ClassReady h) (hs : Saturated h)
    (hp : parent < h.objs.size) (hep : eParent < h.objs.size) :
    ClassReady (Subclass.heap h d name q parent eParent) := by
  have ho := hc.chains.boot.2.2.2.2
  obtain ⟨e, he, hb⟩ := hc.objectEigen
  refine ⟨Subclass.chainsIn hc.chains hp hep, ⟨e, ?_, ?_⟩, ?_, ?_, hc.constRefs.subclass ho, ?_⟩
  · rw [(Subclass.fields ho).2.2.1]; exact he
  · rw [Subclass.ancestors_old hc.chains hs (hc.chains.eigen _ ho _ he)]; exact hb
  · rw [Subclass.ancestors_old hc.chains hs hc.chains.boot.1]; exact hc.classBasic
  · intro e' he' base ch hbase
    rw [(Subclass.fields ho).2.2.1] at he'
    exact hc.eigenSeparate e' he' base ch hbase
  · rw [Subclass.ancestors_old hc.chains hs ho]; exact hc.objectChain

#print axioms ConstRefsLive.subclass
#print axioms ClassReady.subclass
end Ratchet.Denote
