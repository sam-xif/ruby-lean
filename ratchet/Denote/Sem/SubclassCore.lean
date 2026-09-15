import Denote.Sem.SubclassNames
import Denote.Sem.SubclassQueries

/-! Core names and payload conformance through fresh subclass registration. No old object
equality is assumed for the namespace owner, whose constant table changes. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name q : String} {parent eParent : ObjId}
local notation "h₁" => heap h Boot.objectId name q parent eParent

theorem stringPayload (hc : ChainsIn h) (hp : StringPayloadOk h) : StringPayloadOk h₁ := by
  intro o hco
  by_cases hl : o < h.objs.size
  · rw [classOf_old hl] at hco
    obtain ⟨s, hs⟩ := hp o hco
    have hn : h.classPayload? o = none := by simp only [Heap.classPayload?, hs]
    exact ⟨s, by rw [get_old_nonclass hl hn]; exact hs⟩
  · by_cases hk : o = h.objs.size
    · subst o
      rw [classOf_class] at hco
      have hstr := Nat.lt_of_le_of_lt (by decide : Boot.stringId ≤ Boot.procId) hc.boot.2.2.2.1
      exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_of_lt hstr)) hco.symm)
    · by_cases he : o = h.objs.size + 1
      · subst o; rw [classOf_eigen] at hco; cases hco
      · rw [classOf_oob _ (by rw [size]; exact Nat.le_of_not_lt (not_lt_add_two hl hk he))] at hco
        cases hco

theorem arrayPayload (hp : ArrayPayloadOk h) : ArrayPayloadOk h₁ := by
  intro o xs hx
  have hn : (h₁).classPayload? o = none := by simp only [Heap.classPayload?, hx]
  have hg := get_nonclass hn
  rw [hg] at hx
  simpa only [classOf, hg] using hp o xs hx

theorem hashPayload (hp : HashPayloadOk h) : HashPayloadOk h₁ := by
  intro o xs hx
  have hn : (h₁).classPayload? o = none := by simp only [Heap.classPayload?, hx]
  have hg := get_nonclass hn
  rw [hg] at hx
  simpa only [classOf, hg] using hp o xs hx

theorem core (hc : CoreOk h) (hs : Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) (hp : parent < h.objs.size) (he : eParent < h.objs.size) :
    CoreOk h₁ := by
  have hch := hc.classReady.chains
  have hl : ∀ k, k ≤ Boot.procId → k < h.objs.size :=
    fun _ hk => Nat.lt_of_le_of_lt hk hch.boot.2.2.2.1
  have hr := hc.classReady.constRefs "Regexp" _ (classNamed_constOwn hc.regexpNamed)
  refine {
    classReady := hc.classReady.subclass hs hp he
    rootNames := rootNames hc.rootNames hc.classReady.constRefs ho hn
    basicSelf := ?_
    stringNamed := named hch.boot.2.2.2.2 hn hc.stringNamed
    stringSelf := ?_
    stringBasic := ?_
    regexpNamed := named hch.boot.2.2.2.2 hn hc.regexpNamed
    regexpSelf := ?_
    regexpBasic := ?_
    procBasic := ?_
    arrayBasic := ?_
    hashBasic := ?_
    coreNamed := ?_ }
  · rw [ancestors_old hch hs (hl _ (by decide))]; exact hc.basicSelf
  · rw [ancestors_old hch hs (hl _ (by decide))]; exact hc.stringSelf
  · rw [ancestors_old hch hs (hl _ (by decide))]; exact hc.stringBasic
  · rw [ancestors_old hch hs hr]; exact hc.regexpSelf
  · rw [ancestors_old hch hs hr]; exact hc.regexpBasic
  · rw [ancestors_old hch hs (hl _ (by decide))]; exact hc.procBasic
  · rw [ancestors_old hch hs (hl _ (by decide))]; exact hc.arrayBasic
  · rw [ancestors_old hch hs (hl _ (by decide))]; exact hc.hashBasic
  · intro cn hcn v hv
    by_cases hn' : cn = name
    · subst cn
      rw [const_self ho] at hv; cases hv
      exact ⟨h.objs.size, rfl, by simp only [Heap.classPayload?, get_class, classObjE, Option.isSome_some]⟩
    · rw [const_other hch.boot.2.2.2.2 hn'] at hv
      obtain ⟨o, rfl, hp'⟩ := hc.coreNamed cn hcn v hv
      exact ⟨o, rfl, classPayload_live hp'⟩

#print axioms stringPayload
#print axioms arrayPayload
#print axioms hashPayload
#print axioms core
end Ratchet.Denote.Subclass
