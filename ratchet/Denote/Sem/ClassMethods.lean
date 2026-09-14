import Denote.Sem.ClassHeap

/-! Creating an empty class preserves installed method tables, not just dispatch results.
The positive tables still describe only executed definitions, never the future class body. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem own_methods (ho : Boot.objectId < h.objs.size) (k : ObjId) :
    (((h₁).classPayload? k).map ClassPayload.methods).getD [] =
      ((h.classPayload? k).map ClassPayload.methods).getD [] := by
  by_cases hl : k < h.objs.size
  · rw [Proof.Judgment.freshClsHeap_cp_old ho hl]
    change (((constSetIn h Boot.objectId name (.ref h.objs.size)).classPayload? k).map
      ClassPayload.methods).getD [] = _
    rw [Proof.methods_constSetIn]
  · have hp := Proof.classPayload?_oob h k hl
    by_cases hk : k = h.objs.size
    · subst k; rw [Proof.Judgment.freshClsHeap_cp_k, hp]; rfl
    · by_cases he' : k = h.objs.size + 1
      · subst k; rw [Proof.Judgment.freshClsHeap_cp_e, hp]; rfl
      · rw [Proof.Judgment.freshClsHeap_cp_oob
          (Nat.le_of_not_lt (Proof.Judgment.not_lt_add_two hl hk he')), hp]

theorem own_code (ho : Boot.objectId < h.objs.size) (k : ObjId) (mn : String) :
    ((h₁).classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) =
      (h.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) := by
  have row (heap : Heap) :
      (heap.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) =
        ((((heap.classPayload? k).map ClassPayload.methods).getD []).find? (·.1 == mn)).map (·.2) := by
    cases heap.classPayload? k <;> rfl
  rw [row, row, own_methods ho]

variable {m n : Machine} {κ : Ctx}

theorem classes (ho : Boot.objectId < m.heap.objs.size)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) {C : CTable}
    (hp : ClassesOk C m) : ClassesOk C n := by
  intro c hc
  obtain ⟨k, hk, hmethods⟩ := hp c hc
  refine ⟨k, ?_, ?_⟩
  · rw [hh]; exact named ho hn hk
  · intro d hd
    obtain ⟨md, hm, hrest⟩ := hmethods d hd
    exact ⟨md, by rw [hh, own_code ho]; exact hm, hrest⟩

theorem defs (ho : Boot.objectId < m.heap.objs.size)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) {D : DefTable}
    (hp : DefsOk D m) : DefsOk D n := by
  intro d hd
  obtain ⟨md, hm, hrest⟩ := hp d hd
  exact ⟨md, by rw [hh, own_code ho]; exact hm, hrest⟩

theorem methodsExact (ho : Boot.objectId < m.heap.objs.size)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e)
    (hp : MethodsExact κ m) : MethodsExact κ n := by
  intro k cp hc mn md hm
  have heq := own_methods (name := name) (e := e) ho k
  rw [← hh, hc] at heq
  cases hcp : m.heap.classPayload? k with
  | none => simp only [hcp, Option.map_none, Option.getD_none, Option.map_some,
      Option.getD_some] at heq; rw [heq] at hm; contradiction
  | some cp₀ =>
    simp only [hcp, Option.map_some, Option.getD_some] at heq
    exact hp k cp₀ hcp mn md (heq ▸ hm)

#print axioms own_code
#print axioms classes
#print axioms defs
#print axioms methodsExact
end Ratchet.Denote.FreshClass
