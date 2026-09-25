import Denote.Sem.Module.ModuleData

/-! Heap readiness after fresh module registration. Ordinary class readiness survives;
the new module's metaclass is rooted through the separately retained Module ancestry. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModule
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem constRefs (hc : ConstRefsLive h) (ho : Boot.objectId < h.objs.size) :
    ConstRefsLive h₁ := by
  intro cn k hk
  rw [constOwn_old_fresh ho ho] at hk
  have hl : k = h.objs.size ∨ k < h.objs.size := by
    by_cases hn : cn = name
    · subst cn
      cases hp : h.classPayload? Boot.objectId with
      | none => simp [hmidOf, constSetIn, constOwn, hp] at hk
      | some cp =>
        rw [constOwn_constSetIn_self (by simp [hp]) ho] at hk
        exact Or.inl (Value.ref.inj (Option.some.inj hk)).symm
    · rw [constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inr hn)] at hk
      exact Or.inr (hc cn k hk)
  rw [freshModHeap_size]
  rcases hl with rfl | hl
  · exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  · exact Nat.lt_of_lt_of_le hl (Nat.le_add_right _ _)

theorem ready (hc : ClassReady h) (hs : Saturated h) : ClassReady h₁ := by
  have ho := hc.chains.boot.2.2.2.2
  obtain ⟨e, he, hb⟩ := hc.objectEigen
  refine ⟨chainsIn_fresh hc.chains ho, ⟨e, ?_, ?_⟩, ?_, ?_, constRefs hc.constRefs ho, ?_⟩
  · rw [(fields ho).2.2.1]; exact he
  · rw [ancestors_old_fresh hc.chains hs (hc.chains.eigen _ ho _ he)]; exact hb
  · rw [ancestors_old_fresh hc.chains hs hc.chains.boot.1]; exact hc.classBasic
  · intro e' he' base ch hbase
    rw [(fields ho).2.2.1] at he'
    exact hc.eigenSeparate e' he' base ch hbase
  · rw [ancestors_old_fresh hc.chains hs ho]; exact hc.objectChain

theorem moduleBasic (hc : ChainsIn h) (hs : Saturated h)
    (hm : (ancestors h Boot.moduleId).contains Boot.basicObjectId = true) :
    (ancestors h₁ Boot.moduleId).contains Boot.basicObjectId = true := by
  rw [ancestors_old_fresh hc hs hc.boot.2.1]; exact hm

theorem meta_fresh (hc : ChainsIn h) (hs : Saturated h)
    (hm : (ancestors h Boot.moduleId).contains Boot.basicObjectId = true) :
    MetaReady h₁ h.objs.size := by
  refine ⟨h.objs.size + 1, ?_, ?_, ?_⟩
  · rw [freshModHeap_get_k]
  · rw [ancestors_fresh_e hc hs]
    simp only [List.contains_cons, hm, Bool.or_true]
  · intro base ch hbase
    exact (Nat.ne_of_lt (Nat.lt_succ_of_lt
      (Nat.lt_of_le_of_lt (builtinBase_bound hbase).1 hc.boot.2.2.2.1))).symm

theorem meta_old {k : ObjId} (hm : MetaReady h k)
    (hc : ChainsIn h) (hs : Saturated h) (hk : k < h.objs.size) : MetaReady h₁ k :=
  hm.transport (fields hk).2.2.1
    (fun e he => ancestors_old_fresh hc hs (hc.eigen k hk e he))

#print axioms ready
#print axioms meta_fresh
end Ratchet.Denote.FreshModule
