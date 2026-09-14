import Denote.Sem.ClassDispatch

/-! Builtin conformance across fresh class creation: payloads, primitive dispatch/errors,
and core nominal names. No whole-object agreement is assumed for the constant owner. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem primitiveDispatch (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (free : String → Bool) : primitiveDispatchB h₁ free = primitiveDispatchB h free := by
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

theorem primitiveErrors (hc : Proof.ChainsIn h) (hs : Proof.Saturated h) :
    primitiveErrorsB h₁ = primitiveErrorsB h := by
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
  simp only [primitiveErrorB, Proof.Judgment.ancestors_old_freshC hc hs hl]

theorem stringPayload (hc : Proof.ChainsIn h) (hp : StringPayloadOk h) : StringPayloadOk h₁ := by
  intro o hco
  by_cases hl : o < h.objs.size
  · rw [classOf_old hl] at hco
    obtain ⟨s, hs⟩ := hp o hco
    have hn : h.classPayload? o = none := by simp only [Heap.classPayload?, hs]
    exact ⟨s, by rw [get_old_nonclass hl hn]; exact hs⟩
  · by_cases hk : o = h.objs.size
    · subst o
      rw [Proof.Judgment.classOf_freshC_k] at hco
      have hstr := Nat.lt_of_le_of_lt (by decide : Boot.stringId ≤ Boot.procId) hc.boot.2.2.2.1
      exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_of_lt hstr)) hco.symm)
    · by_cases he' : o = h.objs.size + 1
      · subst o; rw [Proof.Judgment.classOf_freshC_e] at hco; cases hco
      · have hout := Nat.le_of_not_lt (Proof.Judgment.not_lt_add_two hl hk he')
        rw [classOf_oob _ (by rw [Proof.Judgment.freshClsHeap_size]; exact hout)] at hco
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

theorem named_live {cn : String} {k : ObjId} (hn : classNamed? h cn = some k) :
    k < h.objs.size := by
  unfold classNamed? at hn
  split at hn
  · split at hn
    · rename_i hp
      cases hn
      exact lt_size_of_classPayload hp
    · cases hn
  · cases hn

theorem core (hc : CoreOk h) (hs : Proof.Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) (he : (h.get Boot.objectId).eigen = some e) :
    CoreOk h₁ := by
  have hch := hc.classReady.chains
  have hl : ∀ k, k ≤ Boot.procId → k < h.objs.size :=
    fun _ hk => Nat.lt_of_le_of_lt hk hch.boot.2.2.2.1
  have hr := named_live hc.regexpNamed
  refine {
    classReady := hc.classReady.freshClass hs hch.boot.2.2.2.2 he
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
  · rw [Proof.Judgment.ancestors_old_freshC hch hs (hl _ (by decide))]; exact hc.basicSelf
  · rw [Proof.Judgment.ancestors_old_freshC hch hs (hl _ (by decide))]; exact hc.stringSelf
  · rw [Proof.Judgment.ancestors_old_freshC hch hs (hl _ (by decide))]; exact hc.stringBasic
  · rw [Proof.Judgment.ancestors_old_freshC hch hs hr]; exact hc.regexpSelf
  · rw [Proof.Judgment.ancestors_old_freshC hch hs hr]; exact hc.regexpBasic
  · rw [Proof.Judgment.ancestors_old_freshC hch hs (hl _ (by decide))]; exact hc.procBasic
  · rw [Proof.Judgment.ancestors_old_freshC hch hs (hl _ (by decide))]; exact hc.arrayBasic
  · rw [Proof.Judgment.ancestors_old_freshC hch hs (hl _ (by decide))]; exact hc.hashBasic
  · intro cn hcn v hv
    by_cases hn' : cn = name
    · subst cn
      have hnew : constLookup h₁ name = some (.ref h.objs.size) := by
        rw [constLookup_eq_own, Proof.Judgment.constOwn_old_freshC hch.boot.2.2.2.2 hch.boot.2.2.2.2]
        exact Proof.Judgment.constOwn_constSetIn_self ho hch.boot.2.2.2.2
      rw [hnew] at hv
      cases hv
      exact ⟨h.objs.size, rfl, by rw [Proof.Judgment.freshClsHeap_cp_k]; rfl⟩
    · rw [const_other hch.boot.2.2.2.2 hn'] at hv
      obtain ⟨o, rfl, hp⟩ := hc.coreNamed cn hcn v hv
      exact ⟨o, rfl, classPayload_live hp⟩

#print axioms primitiveDispatch
#print axioms primitiveErrors
#print axioms stringPayload
#print axioms arrayPayload
#print axioms hashPayload
#print axioms core
end Ratchet.Denote.FreshClass
