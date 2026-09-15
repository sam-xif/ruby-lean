import Denote.Sem.SubclassGlobals
import Denote.Sem.ClassDeclared
import Denote.Sem.ClassShape

/-! Fresh class creation preserves old allocation capabilities and establishes a new one.
The cached Regexp id supplies a live boot id above Math; freshness excludes that special case. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore
open RubyCore.Proof.Judgment (freshClsHeap)

theorem allocators {h : Heap} {names : List String} {name : String} {e : ObjId}
    (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (hn : constOwn h Boot.objectId name = none) (ha : AllocatorsOk names h) :
    AllocatorsOk names (freshClsHeap h Boot.objectId name name e) := by
  exact Subclass.allocators hc hs hn ha

theorem plain {h : Heap} {d : ObjId} {name q : String} {e : ObjId}
    (hc : CoreOk h) (hs : Proof.Saturated h) :
    PlainAllocator (freshClsHeap h d name q e) h.objs.size := by
  have hr := named_live hc.regexpNamed
  exact (ordinary hc.classReady hs).plain
    (Nat.ne_of_lt (Nat.lt_of_le_of_lt (by decide : Boot.mathId ≤ Boot.regexpId) hr)).symm

#print axioms allocators
#print axioms plain
end Ratchet.Denote.FreshClass
