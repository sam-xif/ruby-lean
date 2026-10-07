import Books.TypeSoundness.Conformance.Class.ClassScopeActual

/-! The fresh body's self dispatch maps to the parent metaclass. Retained instance-name
facts cannot supply this obligation; use the parent's separately retained classNames. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClassActual
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment
variable {p : ObjId}

variable {κ : Ctx} {m : Machine} {name : String} {e : ObjId} {body : RubyCore.Expr}
local notation "entry" => machine m name e body p

theorem nameFree (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hel : e < m.heap.objs.size)
    (hparent : NamesAt (nameFreeN κ) m.heap e) (hn : NameFreeOk κ m) : NameFreeOk κ entry := by
  intro mn hmn k hk owner md hm
  rcases List.mem_cons.mp hk with hk | hk
  · subst k
    rw [current_frame] at hm
    change Interp.methodOn (heap m name e p)
      (classOf (heap m name e p) (.ref m.heap.objs.size)) mn = _ at hm
    rw [classOf_class hd, method_eigen hc hs hd hel] at hm
    exact hparent mn hmn owner md hm
  · rcases List.mem_cons.mp hk with hk | hk
    · subst k
      change Interp.methodOn (heap m name e p)
        (classOf (heap m name e p) (.ref Boot.objectId)) mn = _ at hm
      rw [classOf_old hd hc.boot.2.2.2.2, method_old hc hs hd (ClsGrow.classOf_lt hc hc.boot.2.2.2.2)] at hm
      exact hn mn hmn _ (by simp [nameFreeSites]) owner md hm
    · have heq := List.mem_singleton.mp hk
      subst k
      change Interp.methodOn (heap m name e p) Boot.objectId mn = _ at hm
      rw [method_old hc hs hd hc.boot.2.2.2.2] at hm
      exact hn mn hmn _ (by simp [nameFreeSites]) owner md hm

#print axioms nameFree
end Checker.Soundness.FreshClassActual
