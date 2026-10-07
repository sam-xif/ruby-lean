import Books.TypeSoundness.Conformance.Module.ModuleScopeActual
import Books.TypeSoundness.Conformance.Class.ClassNameEntryActual

/-! The module body's self dispatch maps to Module (moduleBase.names). -/

set_option autoImplicit false
namespace Checker.Soundness.FreshModuleActual
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment

variable {κ : Ctx} {m : Machine} {name : String}  {body : RubyCore.Expr}
local notation "entry" => machine m name body

theorem nameFree (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size)
    (hparent : NamesAt (nameFreeN κ) m.heap Boot.moduleId) (hn : NameFreeOk κ m) : NameFreeOk κ entry := by
  intro mn hmn k hk owner md hm
  rcases List.mem_cons.mp hk with hk | hk
  · subst k
    rw [current_frame] at hm
    change Interp.methodOn (heap m name)
      (classOf (heap m name) (.ref m.heap.objs.size)) mn = _ at hm
    rw [classOf_module hd, method_eigen hc hs hd] at hm
    exact hparent mn hmn owner md hm
  · rcases List.mem_cons.mp hk with hk | hk
    · subst k
      change Interp.methodOn (heap m name)
        (classOf (heap m name) (.ref Boot.objectId)) mn = _ at hm
      rw [classOf_old hd hc.boot.2.2.2.2, method_old hc hs hd (ClsGrow.classOf_lt hc hc.boot.2.2.2.2)] at hm
      exact hn mn hmn _ (by simp [nameFreeSites]) owner md hm
    · have heq := List.mem_singleton.mp hk
      subst k
      change Interp.methodOn (heap m name) Boot.objectId mn = _ at hm
      rw [method_old hc hs hd hc.boot.2.2.2.2] at hm
      exact hn mn hmn _ (by simp [nameFreeSites]) owner md hm

#print axioms nameFree
end Checker.Soundness.FreshModuleActual
