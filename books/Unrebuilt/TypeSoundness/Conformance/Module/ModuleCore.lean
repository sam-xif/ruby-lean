import Books.TypeSoundness.Conformance.Module.ModuleConstants

/-! Core heap conformance and data-payload shapes after fresh module registration.
The new module and eigenclass are excluded from every data-payload case explicitly. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshModule
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem namesOk (hc : ChainsIn h) (hn : NamesOk h) (hne : name.isEmpty = false) : NamesOk h₁ := by
  apply namesOk_namedGrow clsGrow_hmid_fresh.size clsGrow_hmid_fresh.get
    (namesOk_constSetIn hn Boot.objectId name (.ref h.objs.size))
  intro k hk cp hp
  rw [hmid_size] at hk
  by_cases heq : k = h.objs.size
  · subst k
    rw [freshModHeap_cp_k] at hp
    cases hp
    refine ⟨rfl, hne, ?_⟩
    rw [classOf_fresh_k, freshModHeap_size]
    exact Nat.lt_succ_self _
  · by_cases heq' : k = h.objs.size + 1
    · subst k
      rw [freshModHeap_cp_e] at hp
      cases hp
      refine ⟨rfl, ?_, ?_⟩
      · apply Bool.eq_false_iff.mpr
        intro he
        rw [String.isEmpty_iff] at he
        have hh := congrArg String.length he
        simp [String.length_append] at hh
      · rw [classOf_fresh_e, freshModHeap_size]
        exact Nat.lt_of_lt_of_le hc.boot.1 (Nat.le_add_right _ _)
    · rw [freshModHeap_cp_oob (by omega)] at hp
      contradiction

theorem stringPayload (hc : ChainsIn h) (hp : StringPayloadOk h) : StringPayloadOk h₁ := by
  intro o hco
  by_cases hl : o < h.objs.size
  · rw [classOf_old hl] at hco
    obtain ⟨s, hs⟩ := hp o hco
    have hn : h.classPayload? o = none := by simp only [Heap.classPayload?, hs]
    exact ⟨s, by rw [get_old_nonclass hl hn]; exact hs⟩
  · by_cases hk : o = h.objs.size
    · subst o
      rw [classOf_fresh_k] at hco
      have hstr := Nat.lt_of_le_of_lt (by decide : Boot.stringId ≤ Boot.procId) hc.boot.2.2.2.1
      exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_of_lt hstr)) hco.symm)
    · by_cases he : o = h.objs.size + 1
      · subst o; rw [classOf_fresh_e] at hco; cases hco
      · rw [classOf_oob _ (by rw [freshModHeap_size]; exact Nat.le_of_not_lt (not_lt_add_two hl hk he))] at hco
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
    (hn : constOwn h Boot.objectId name = none) : CoreOk h₁ := by
  have hch := hc.classReady.chains
  have hl : ∀ k, k ≤ Boot.procId → k < h.objs.size :=
    fun _ hk => Nat.lt_of_le_of_lt hk hch.boot.2.2.2.1
  have hr := hc.classReady.constRefs "Regexp" _ (classNamed_constOwn hc.regexpNamed)
  refine {
    classReady := ready hc.classReady hs
    rootNames := rootNames hc.rootNames hc.classReady.constRefs ho hn
    metaConstants := by
      rw [classOf_old hch.boot.2.2.2.2]
      exact fallback_old hch hs ho (ClsGrow.classOf_lt hch hch.boot.2.2.2.2) hc.metaConstants
    basicSelf := ?_
    moduleBasic := moduleBasic hch hs hc.moduleBasic
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
  · rw [ancestors_old_fresh hch hs (hl _ (by decide))]; exact hc.basicSelf
  · rw [ancestors_old_fresh hch hs (hl _ (by decide))]; exact hc.stringSelf
  · rw [ancestors_old_fresh hch hs (hl _ (by decide))]; exact hc.stringBasic
  · rw [ancestors_old_fresh hch hs hr]; exact hc.regexpSelf
  · rw [ancestors_old_fresh hch hs hr]; exact hc.regexpBasic
  · rw [ancestors_old_fresh hch hs (hl _ (by decide))]; exact hc.procBasic
  · rw [ancestors_old_fresh hch hs (hl _ (by decide))]; exact hc.arrayBasic
  · rw [ancestors_old_fresh hch hs (hl _ (by decide))]; exact hc.hashBasic
  · intro cn hcn v hv
    by_cases hn' : cn = name
    · subst cn
      rw [const_self ho] at hv; cases hv
      exact ⟨h.objs.size, rfl, by simp only [freshModHeap_cp_k, Option.isSome_some]⟩
    · rw [const_other hch.boot.2.2.2.2 hn'] at hv
      obtain ⟨o, rfl, hp'⟩ := hc.coreNamed cn hcn v hv
      exact ⟨o, rfl, classPayload_live hp'⟩

#print axioms core
#print axioms stringPayload
#print axioms arrayPayload
#print axioms hashPayload
end Checker.Soundness.FreshModule
