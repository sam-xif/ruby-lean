import Denote.Sem.SubclassData
import Denote.Sem.RootNames

/-! Global registration and fresh class identity, independent of superclass and display
name. Reverse transport is bounded: dangling references can otherwise become new aliases. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name q : String} {parent eParent : ObjId}
local notation "h₁" => heap h Boot.objectId name q parent eParent

theorem constOwn_old {d o : ObjId} (ho : o < h.objs.size) (cn : String) :
    constOwn (heap h d name q parent eParent) o cn = constOwn (hmidOf h d name) o cn := by
  unfold constOwn Heap.classPayload?
  rw [get_old ho]

theorem const_self (ho : (h.classPayload? Boot.objectId).isSome = true) :
    constLookup h₁ name = some (.ref h.objs.size) := by
  rw [const_eq_own, constOwn_old (lt_size_of_classPayload ho)]
  exact constOwn_constSetIn_self ho (lt_size_of_classPayload ho)

theorem named_fresh (ho : (h.classPayload? Boot.objectId).isSome = true) :
    classNamed? h₁ name = some h.objs.size := by
  simp only [classNamed?, const_self ho, Heap.classPayload?, get_class, classObjE,
    Option.isSome_some, ite_true]

theorem named_old_back (ho : (h.classPayload? Boot.objectId).isSome = true)
    {cn : String} {k : ObjId} (hl : k < h.objs.size) (hk : classNamed? h₁ cn = some k) :
    classNamed? h cn = some k := by
  by_cases hn : cn = name
  · subst cn
    rw [named_fresh ho] at hk
    exact False.elim ((Nat.ne_of_lt hl) (Option.some.inj hk).symm)
  · unfold classNamed? at hk ⊢
    rw [const_other (lt_size_of_classPayload ho) hn] at hk
    split at hk
    · split at hk
      · rename_i hp
        cases hk
        have hp₀ : (h.classPayload? k).isSome = true := by
          rw [← classPayload_old_isSome (d := Boot.objectId) (name := name) (q := q)
            (parent := parent) (eParent := eParent) hl]; exact hp
        simp only [hp₀, ite_true]
      · cases hk
    · cases hk

theorem named_fresh_only (hc : ConstRefsLive h) (ho : Boot.objectId < h.objs.size)
    {cn : String} (hk : classNamed? h₁ cn = some h.objs.size) : cn = name := by
  by_cases hn : cn = name
  · exact hn
  have href := classNamed_constOwn hk
  rw [constOwn_old ho, constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inr hn)] at href
  exact False.elim ((Nat.lt_irrefl _) (hc cn h.objs.size href))

theorem rootNames (hc : RootNames h) (hl : ConstRefsLive h)
    (ho : (h.classPayload? Boot.objectId).isSome = true) (hn : constOwn h Boot.objectId name = none) :
    RootNames h₁ := by
  refine ⟨fun cn k hk => named (lt_size_of_classPayload ho) hn (hc.named cn k hk), ?_⟩
  intro cn k hk hr
  exact hc.only cn k (named_old_back ho (hc.live hl hr) hk) hr

#print axioms named_fresh
#print axioms named_fresh_only
#print axioms rootNames
end Ratchet.Denote.Subclass
