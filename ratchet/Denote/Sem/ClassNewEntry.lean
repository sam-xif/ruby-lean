import Denote.Sem.ClassQueries

/-! A fresh ordinary class inherits Object's class-object constructor dispatch.
The native-shadow guard is additional to method lookup, as in ordinary sends. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

theorem new_dispatch {h : Heap} {name : String} {e : ObjId}
    (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (he : (h.get Boot.objectId).eigen = some e) (hne : name.isEmpty = false)
    (hn : NativeQuiet name "new") (hd : NewDispatch h (classOf h (.ref Boot.objectId))) :
    NewDispatch (freshClsHeap h Boot.objectId name name e)
      (classOf (freshClsHeap h Boot.objectId name name e) (.ref h.objs.size)) := by
  have hel := hc.eigen Boot.objectId hc.boot.2.2.2.2 e he
  have hm (mn : String) :
      Interp.methodOn (freshClsHeap h Boot.objectId name name e)
        (classOf (freshClsHeap h Boot.objectId name name e) (.ref h.objs.size)) mn =
      Interp.methodOn h (classOf h (.ref Boot.objectId)) mn := by
    rw [Proof.Judgment.classOf_freshC_k, method_parent hc hs hel]
    simp only [parent, if_neg (Nat.succ_ne_self _), ite_true, classOf, he]
  refine ⟨?_, ?_⟩
  · intro owner md hl
    obtain ⟨hb, hu, hv, hp, hshadow⟩ := hd.found owner md ((hm "new").symm ▸ hl)
    refine ⟨hb, hu, hv, hp, ?_⟩
    rw [Proof.Judgment.classOf_freshC_k]
    apply shadow_before_parent hc hs hel hne hn.1 hn.2
    simpa only [parent, if_neg (Nat.succ_ne_self _), ite_true, classOf, he] using hshadow
  · intro hl owner md hmd
    exact hd.missing ((hm "new").symm ▸ hl) owner md ((hm "method_missing").symm ▸ hmd)

#print axioms new_dispatch
end Ratchet.Denote.FreshClass
