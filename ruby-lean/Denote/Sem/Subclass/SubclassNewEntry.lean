import Denote.Sem.Subclass.SubclassQueries

/-! Fresh class-object constructor lookup follows the parent's metaclass. No callable
initializer is inferred from the fresh class's empty own-method table. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet

theorem new_dispatch {h : Heap} {d parent eParent : ObjId} {name q : String}
    (hc : Proof.ChainsIn h) (hs : Proof.Saturated h) (hp : parent < h.objs.size)
    (he : (h.get parent).eigen = some eParent) (hne : q.isEmpty = false)
    (hn : FreshClass.NativeQuiet q "new") (hd : NewDispatch h (classOf h (.ref parent))) :
    NewDispatch (heap h d name q parent eParent)
      (classOf (heap h d name q parent eParent) (.ref h.objs.size)) := by
  have hel := hc.eigen parent hp eParent he
  have hm (mn : String) :
      Interp.methodOn (heap h d name q parent eParent)
        (classOf (heap h d name q parent eParent) (.ref h.objs.size)) mn =
      Interp.methodOn h (classOf h (.ref parent)) mn := by
    rw [classOf_class, method_eigen hc hs hel]
    simp only [classOf, he]
  refine ⟨?_, ?_⟩
  · intro owner md hl
    obtain ⟨hb, hu, hv, hpre, hshadow⟩ := hd.found owner md ((hm "new").symm ▸ hl)
    refine ⟨hb, hu, hv, hpre, ?_⟩
    rw [classOf_class]
    apply shadow_before_source hc hs hp hel hne hn.1 hn.2
    simpa only [source, if_neg (Nat.succ_ne_self _), ite_true, classOf, he] using hshadow
  · intro hl owner md hmd
    exact hd.missing ((hm "new").symm ▸ hl) owner md ((hm "method_missing").symm ▸ hmd)

#print axioms new_dispatch
end Ratchet.Denote.Subclass
