import Denote.Sem.ClassBases

/-! A fresh class has only its newly registered global name. Existing class aliases remain
valid; the input condition rules out dangling references becoming new aliases on allocation. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

theorem named_fresh_only {h : Heap} {name cn : String} {e : ObjId}
    (hc : ConstRefsLive h) (ho : Boot.objectId < h.objs.size)
    (hk : classNamed? (freshClsHeap h Boot.objectId name name e) cn = some h.objs.size) :
    cn = name := by
  by_cases hne : cn = name
  · exact hne
  exfalso
  have href := classNamed_constOwn hk
  rw [Proof.Judgment.constOwn_old_freshC ho ho] at href
  change constOwn (constSetIn h Boot.objectId name (.ref h.objs.size)) Boot.objectId cn =
    some (.ref h.objs.size) at href
  rw [Proof.constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inr hne)] at href
  exact (Nat.lt_irrefl _) (hc cn h.objs.size href)

#print axioms named_fresh_only
end Ratchet.Denote.FreshClass
