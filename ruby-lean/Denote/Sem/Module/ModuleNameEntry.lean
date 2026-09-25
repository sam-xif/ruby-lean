import Denote.Sem.Module.ModuleFrame
import Denote.Sem.Module.ModuleDispatch

/-! Module-body self dispatches through the separately retained Module base. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModule
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {κ : Ctx} {m : Machine} {name : String} {body : RubyCore.Expr}
local notation "entry" => freshModMachine m Boot.objectId m.currentFrame.cref name name body

theorem nameFree (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hp : ModuleBase κ m.heap) (hn : NameFreeOk κ m) : NameFreeOk κ entry := by
  intro mn hmn k hk owner md hm
  rcases List.mem_cons.mp hk with hk | hk
  · subst k
    rw [current_frame] at hm
    change Interp.methodOn (freshModHeap m.heap Boot.objectId name name)
      (classOf (freshModHeap m.heap Boot.objectId name name) (.ref m.heap.objs.size)) mn = _ at hm
    rw [classOf_fresh_k, method_eigen hc hs] at hm
    exact hp.names mn hmn owner md hm
  · rcases List.mem_cons.mp hk with hk | hk
    · subst k
      change Interp.methodOn (freshModHeap m.heap Boot.objectId name name)
        (classOf (freshModHeap m.heap Boot.objectId name name) (.ref Boot.objectId)) mn = _ at hm
      rw [classOf_old hc.boot.2.2.2.2, method_old hc hs (ClsGrow.classOf_lt hc hc.boot.2.2.2.2)] at hm
      exact hn mn hmn _ (by simp [nameFreeSites]) owner md hm
    · have heq := List.mem_singleton.mp hk
      subst k
      change Interp.methodOn (freshModHeap m.heap Boot.objectId name name) Boot.objectId mn = _ at hm
      rw [method_old hc hs hc.boot.2.2.2.2] at hm
      exact hn mn hmn _ (by simp [nameFreeSites]) owner md hm

#print axioms nameFree
end Ratchet.Denote.FreshModule
