import Denote.Sem.Module.ModuleNames

/-! Module allocation creates empty method tables and preserves all installed code,
including old singleton owners. No future module body is published here. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModule
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem own_methods (k : ObjId) :
    (((h₁).classPayload? k).map ClassPayload.methods).getD [] =
      ((h.classPayload? k).map ClassPayload.methods).getD [] := by
  by_cases hl : k < h.objs.size
  · rw [clsGrow_hmid_fresh.payloadOld (by rwa [hmid_size])]
    rw [methods_constSetIn]
  · have hp := classPayload?_oob h k hl
    by_cases hk : k = h.objs.size
    · subst k; rw [hp, freshModHeap_cp_k]; rfl
    · by_cases he : k = h.objs.size + 1
      · subst k; rw [hp, freshModHeap_cp_e]; rfl
      · rw [freshModHeap_cp_oob (Nat.le_of_not_lt (not_lt_add_two hl hk he)), hp]

theorem own_code (k : ObjId) (mn : String) :
    ((h₁).classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) =
      (h.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) := by
  have row (g : Heap) :
      (g.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) =
        ((((g.classPayload? k).map ClassPayload.methods).getD []).find? (·.1 == mn)).map (·.2) := by
    cases g.classPayload? k <;> rfl
  rw [row, row, own_methods]

variable {m n : Machine} {κ : Ctx}

theorem classes (ho : Boot.objectId < m.heap.objs.size) (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshModHeap m.heap Boot.objectId name name) {C : CTable}
    (hp : ClassesOk C m) : ClassesOk C n := by
  intro c hc
  obtain ⟨k, hk, hmethods, hsingle⟩ := hp c hc
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [hh]; exact named ho hn hk
  · intro d hd
    obtain ⟨md, hm, hrest⟩ := hmethods d hd
    exact ⟨md, by rw [hh, own_code]; exact hm, hrest⟩
  · rw [hh]
    exact hsingle.transport (named_live hk) (fun o ho => (fields ho).2.2.1) own_code

theorem defs (hh : n.heap = freshModHeap m.heap Boot.objectId name name) {D : DefTable}
    (hp : DefsOk D m) : DefsOk D n := by
  intro d hd
  obtain ⟨md, hm, hrest⟩ := hp d hd
  exact ⟨md, by rw [hh, own_code]; exact hm, hrest⟩

theorem methodsExact (hh : n.heap = freshModHeap m.heap Boot.objectId name name)
    (hp : MethodsExact κ m) : MethodsExact κ n := by
  intro k cp hc mn md hm
  have heq := own_methods (h := m.heap) (name := name) k
  rw [← hh, hc] at heq
  cases hcp : m.heap.classPayload? k with
  | none =>
    simp only [hcp, Option.map_none, Option.getD_none, Option.map_some, Option.getD_some] at heq
    rw [heq] at hm; contradiction
  | some cp₀ =>
    simp only [hcp, Option.map_some, Option.getD_some] at heq
    exact hp k cp₀ hcp mn md (heq ▸ hm)

#print axioms classes
#print axioms methodsExact
end Ratchet.Denote.FreshModule
