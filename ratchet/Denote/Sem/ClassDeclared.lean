import Denote.Sem.SubclassDeclared
import Denote.Sem.ClassBases
import Denote.Sem.ClassCore

/-! Fresh registration preserves declarations about already-installed classes. Constructor
dispatch and both directions of named ancestry remain intact.
The new class is not inserted into the positive table by this transport lemma. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem module_old (_ho : Boot.objectId < h.objs.size) {k : ObjId} (hk : k < h.objs.size) :
    ((h₁).classPayload? k).map (·.isModule) = (h.classPayload? k).map (·.isModule) :=
  Subclass.module_old hk

variable {κ : Ctx} {m n : Machine}

theorem declared (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e)
    (hclasses : ClassesOk κ.classes m) (hp : DeclClassOk κ m) : DeclClassOk κ n :=
  Subclass.declared hc hs ho hn hh hclasses hp

#print axioms module_old
#print axioms declared
end Ratchet.Denote.FreshClass
