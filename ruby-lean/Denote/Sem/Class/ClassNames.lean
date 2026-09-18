import Denote.Sem.Class.ClassDispatch
import Denote.Sem.Class.ClassFrame
import Denote.Sem.Subclass.SubclassNameEntry

/-! Fresh class self inherits Object's metaclass dispatch, already covered by NameFreeOk.
No assumption about unrelated class objects or prelude methods is needed. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine freshModFrame)

variable {κ : Ctx} {m : Machine} {name : String} {e : ObjId} {body : RubyCore.Expr}
local notation "entry" => freshClsMachine m Boot.objectId m.currentFrame.cref name name e body

theorem name_site_parent (hc : Proof.ChainsIn m.heap)
    (he : (m.heap.get Boot.objectId).eigen = some e) {k : ObjId}
    (hk : k ∈ nameFreeSites entry) : parent m.heap e k ∈ nameFreeSites m := by
  have ho := hc.boot.2.2.2.2
  have hco : classOf m.heap (.ref Boot.objectId) = e := by simp only [classOf, he]
  rcases List.mem_cons.mp hk with hk | hk
  · subst k
    rw [current_frame]
    change parent m.heap e
      (classOf (freshClsHeap m.heap Boot.objectId name name e) (.ref m.heap.objs.size)) ∈ _
    rw [Proof.Judgment.classOf_freshC_k]
    simp only [parent, if_neg (Nat.succ_ne_self _), ite_true]
    simp [nameFreeSites, hco]
  · rcases List.mem_cons.mp hk with hk | hk
    · subst k
      change parent m.heap e
        (classOf (freshClsHeap m.heap Boot.objectId name name e) (.ref Boot.objectId)) ∈ _
      rw [classOf_old ho, parent_old (Proof.ClsGrow.classOf_lt hc ho)]
      simp [nameFreeSites]
    · have hk := List.mem_singleton.mp hk
      subst k
      rw [parent_old ho]
      simp [nameFreeSites]

theorem nameFree (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hn : NameFreeOk κ m) :
    NameFreeOk κ entry := by
  have hel := hc.eigen Boot.objectId hc.boot.2.2.2.2 e he
  apply Subclass.nameFree hc hs hel _ hn
  intro mn hmn owner md hm
  have hco : classOf m.heap (.ref Boot.objectId) = e := by simp only [classOf, he]
  exact hn mn hmn e (by simp [nameFreeSites, hco]) owner md hm

#print axioms name_site_parent
#print axioms nameFree
end Ratchet.Denote.FreshClass
