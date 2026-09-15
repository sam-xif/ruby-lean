import Denote.Sem.ClassConstants
import Denote.Sem.ClassCore
import Denote.Sem.SubclassTables

/-! Default-superclass constant-table transport specializes the shared subclass proofs. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)
variable {κ : Ctx} {m n : Machine} {name : String} {e : ObjId}

theorem constants (ho : Boot.objectId < m.heap.objs.size)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e)
    (hd : DataPres m.heap n.heap) (hs : ConstScopeOk m) (hs' : ConstScopeOk n)
    (hf : ∀ cn τ, constGet? κ cn = some τ → FirstOrder τ = true)
    (hp : ConstsOk κ m) : ConstsOk κ n := Subclass.constants ho hn hh hd hs hs' hf hp

theorem paths (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e)
    (hd : DataPres m.heap n.heap) (hf : ClassTablesFrame κ name m)
    (hp : ConstPathsOk κ m) : ConstPathsOk κ n := Subclass.paths hc hs hn hh hd hf hp

theorem nested (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e)
    (hd : DataPres m.heap n.heap) (hf : ClassTablesFrame κ name m)
    (hp : NestedClassesOk κ.classes m) : NestedClassesOk κ.classes n := Subclass.nested hc hs hn hh hd hf hp

#print axioms constants
#print axioms paths
#print axioms nested
end Ratchet.Denote.FreshClass
