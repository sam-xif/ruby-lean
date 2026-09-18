import Denote.Sem.Class.ClassBases

/-! A fresh class has only its newly registered global name. Existing class aliases remain
valid; the input condition rules out dangling references becoming new aliases on allocation. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

theorem named_fresh_only {h : Heap} {name cn : String} {e : ObjId}
    (hc : ConstRefsLive h) (ho : Boot.objectId < h.objs.size)
    (hk : classNamed? (freshClsHeap h Boot.objectId name name e) cn = some h.objs.size) :
    cn = name := Subclass.named_fresh_only hc ho hk

#print axioms named_fresh_only
end Ratchet.Denote.FreshClass
