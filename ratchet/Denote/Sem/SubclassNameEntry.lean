import Denote.Sem.SubclassFrame
import Denote.Sem.SubclassDispatch

/-! The fresh body's self dispatch maps to the parent metaclass. Retained instance-name
facts cannot supply this obligation; use the parent's separately retained classNames. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {κ : Ctx} {m : Machine} {name q : String} {parent eParent : ObjId} {body : RubyCore.Expr}
local notation "entry" => machine m Boot.objectId m.currentFrame.cref name q parent eParent body

theorem nameFree (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hel : eParent < m.heap.objs.size)
    (hparent : NamesAt (nameFreeN κ) m.heap eParent) (hn : NameFreeOk κ m) : NameFreeOk κ entry := by
  intro mn hmn k hk owner md hm
  rcases List.mem_cons.mp hk with hk | hk
  · subst k
    rw [current_frame] at hm
    change Interp.methodOn (heap m.heap Boot.objectId name q parent eParent)
      (classOf (heap m.heap Boot.objectId name q parent eParent) (.ref m.heap.objs.size)) mn = _ at hm
    rw [classOf_class, method_eigen hc hs hel] at hm
    exact hparent mn hmn owner md hm
  · rcases List.mem_cons.mp hk with hk | hk
    · subst k
      change Interp.methodOn (heap m.heap Boot.objectId name q parent eParent)
        (classOf (heap m.heap Boot.objectId name q parent eParent) (.ref Boot.objectId)) mn = _ at hm
      rw [classOf_old hc.boot.2.2.2.2, method_old hc hs (ClsGrow.classOf_lt hc hc.boot.2.2.2.2)] at hm
      exact hn mn hmn _ (by simp [nameFreeSites]) owner md hm
    · have heq := List.mem_singleton.mp hk
      subst k
      change Interp.methodOn (heap m.heap Boot.objectId name q parent eParent) Boot.objectId mn = _ at hm
      rw [method_old hc hs hc.boot.2.2.2.2] at hm
      exact hn mn hmn _ (by simp [nameFreeSites]) owner md hm

#print axioms nameFree
end Ratchet.Denote.Subclass
