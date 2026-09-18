import Denote.Sem.Subclass.SubclassNewEntry
import Denote.Sem.Class.ClassQueries

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
  exact Subclass.new_dispatch hc hs hc.boot.2.2.2.2 he hne hn hd

#print axioms new_dispatch
end Ratchet.Denote.FreshClass
