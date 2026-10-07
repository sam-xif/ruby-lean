import Books.TypeSoundness.Conformance.Module.ModuleData
import Books.TypeSoundness.Conformance.Names.RootNames

/-! Global module registration preserves old names and canonical roots. Reverse
transport is bounded because a dangling reference can become the fresh module. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshModule
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

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

theorem const_self (ho : (h.classPayload? Boot.objectId).isSome = true) :
    constLookup h₁ name = some (.ref h.objs.size) := by
  have hl := lt_size_of_classPayload ho
  rw [const_eq_own, constOwn_old_fresh hl hl]
  exact constOwn_constSetIn_self ho hl

theorem named_old_back (ho : (h.classPayload? Boot.objectId).isSome = true)
    {cn : String} {k : ObjId} (hl : k < h.objs.size) (hk : classNamed? h₁ cn = some k) :
    classNamed? h cn = some k := by
  by_cases hn : cn = name
  · subst cn
    rw [named_new (lt_size_of_classPayload ho) ho] at hk
    exact False.elim ((Nat.ne_of_lt hl) (Option.some.inj hk).symm)
  · unfold classNamed? at hk ⊢
    rw [const_other (lt_size_of_classPayload ho) hn] at hk
    split at hk
    · split at hk
      · rename_i hp
        cases hk
        have hp₀ : (h.classPayload? k).isSome = true := by
          rw [← classPayload_old_isSome (name := name) hl]; exact hp
        simp only [hp₀, ite_true]
      · cases hk
    · cases hk

theorem fresh_name_only (hc : ConstRefsLive h) (ho : Boot.objectId < h.objs.size)
    {cn : String} (hn : classNamed? h₁ cn = some h.objs.size) : cn = name := by
  by_cases hne : cn = name
  · exact hne
  exfalso
  have hn := classNamed_constOwn hn
  rw [constOwn_old_fresh ho ho,
    constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inr hne)] at hn
  exact (Nat.lt_irrefl _) (hc cn h.objs.size hn)

theorem rootNames (hc : RootNames h) (hl : ConstRefsLive h)
    (ho : (h.classPayload? Boot.objectId).isSome = true) (hn : constOwn h Boot.objectId name = none) :
    RootNames h₁ := by
  refine ⟨fun cn k hk => named (lt_size_of_classPayload ho) hn (hc.named cn k hk), ?_⟩
  intro cn k hk hr
  exact hc.only cn k (named_old_back ho (hc.live hl hr) hk) hr

#print axioms named_old_back
#print axioms rootNames
end Checker.Soundness.FreshModule
