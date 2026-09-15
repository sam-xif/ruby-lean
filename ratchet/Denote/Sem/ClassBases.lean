import Denote.Sem.SubclassBases
import Denote.Sem.ClassHeap
import Denote.Sem.SubclassNames

/-! Fresh default-superclass declarations preserve builtin ancestry answers. The new
metaclass inherits Object's eigenclass, whose identity must be separate from the bases. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

/-- A name resolving to an old class after registration already resolved there before.
Names that held dangling references may acquire a new meaning, but only at a fresh id. -/
theorem named_old_back (ho : (h.classPayload? Boot.objectId).isSome = true)
    {cn : String} {j : ObjId} (hj : j < h.objs.size) (hk : classNamed? h₁ cn = some j) :
    classNamed? h cn = some j := Subclass.named_old_back ho hj hk

variable {κ : Ctx} {m n : Machine}

theorem baseChains (hc : ClassReady m.heap) (hs : Proof.Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (he : (m.heap.get Boot.objectId).eigen = some e)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) (hp : BaseChainsOk κ m) :
    BaseChainsOk κ n :=
  Subclass.baseChains hc hs ho hn hc.chains.boot.2.2.2.2
    (hc.chains.eigen _ hc.chains.boot.2.2.2.2 _ he)
    (fun _ _ hb _ => (builtinBase_bound hb).2.symm)
    (hc.eigenSeparate e he) hh hp

#print axioms named_old_back
#print axioms baseChains
end Ratchet.Denote.FreshClass
