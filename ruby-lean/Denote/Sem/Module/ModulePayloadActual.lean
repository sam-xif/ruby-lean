import Denote.Sem.Module.ModuleQueriesActual
import Denote.Sem.Class.ClassPayloadActual

/-! String/Array/Hash payload transfers at the actual module heap. -/

set_option autoImplicit false
namespace Ratchet.Denote.FreshModuleActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment
variable {m : Machine} {name : String} 
local notation "h₁" => heap m name

theorem stringPayload (hc : ChainsIn m.heap) (hd : m.lexicalNamespace < m.heap.objs.size) (hp : StringPayloadOk m.heap) : StringPayloadOk h₁ := by
  intro o hco
  by_cases hl : o < m.heap.objs.size
  · rw [classOf_old hd hl] at hco
    obtain ⟨s, hs⟩ := hp o hco
    have hn : m.heap.classPayload? o = none := by simp only [Heap.classPayload?, hs]
    exact ⟨s, by rw [get_old_nonclass hd hl hn]; exact hs⟩
  · by_cases hk : o = m.heap.objs.size
    · subst o
      rw [classOf_module hd] at hco
      have hstr := Nat.lt_of_le_of_lt (by decide : Boot.stringId ≤ Boot.procId) hc.boot.2.2.2.1
      exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_of_lt hstr)) hco.symm)
    · by_cases he : o = m.heap.objs.size + 1
      · subst o; rw [classOf_eigen] at hco; cases hco
      · rw [classOf_oob _ (by rw [size m name]; exact Nat.le_of_not_lt (not_lt_add_two hl hk he))] at hco
        cases hco

theorem frozenFields (hd : m.lexicalNamespace < m.heap.objs.size) (hp : FrozenFieldsOk m.heap) :
    FrozenFieldsOk h₁ := by
  apply hp.of_fields
  intro o
  by_cases hl : o < m.heap.objs.size
  · rw [get_old hd hl]; exact Or.inr (fields_constSetIn _ _ _ _ _)
  · left
    by_cases hk : o = m.heap.objs.size
    · subst o; rw [get_module hd]; rfl
    · by_cases he : o = m.heap.objs.size + 1
      · subst o; rw [get_eigen]; rfl
      · rw [get_oob _ (by rw [size m name]; exact Nat.le_of_not_lt (not_lt_add_two hl hk he))]; rfl

theorem arrayPayload (hd : m.lexicalNamespace < m.heap.objs.size) (hp : ArrayPayloadOk m.heap) : ArrayPayloadOk h₁ := by
  intro o xs hx
  have hn : (h₁).classPayload? o = none := by simp only [Heap.classPayload?, hx]
  have hg := get_nonclass hd hn
  rw [hg] at hx
  simpa only [classOf, hg] using hp o xs hx

theorem hashPayload (hd : m.lexicalNamespace < m.heap.objs.size) (hp : HashPayloadOk m.heap) : HashPayloadOk h₁ := by
  intro o xs hx
  have hn : (h₁).classPayload? o = none := by simp only [Heap.classPayload?, hx]
  have hg := get_nonclass hd hn
  rw [hg] at hx
  simpa only [classOf, hg] using hp o xs hx

#print axioms stringPayload
#print axioms arrayPayload
#print axioms hashPayload
end Ratchet.Denote.FreshModuleActual
