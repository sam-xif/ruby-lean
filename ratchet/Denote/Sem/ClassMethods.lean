import Denote.Sem.ClassHeap
import Denote.Sem.SubclassMethods

/-! Creating an empty class preserves installed method tables, not just dispatch results.
The positive tables still describe only executed definitions, never the future class body. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem own_methods (_ho : Boot.objectId < h.objs.size) (k : ObjId) :
    (((h₁).classPayload? k).map ClassPayload.methods).getD [] =
      ((h.classPayload? k).map ClassPayload.methods).getD [] := Subclass.own_methods k

theorem own_code (_ho : Boot.objectId < h.objs.size) (k : ObjId) (mn : String) :
    ((h₁).classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) =
      (h.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == mn)).map (·.2)) := Subclass.own_code k mn

variable {m n : Machine} {κ : Ctx}

theorem classes (ho : Boot.objectId < m.heap.objs.size)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) {C : CTable}
    (hp : ClassesOk C m) : ClassesOk C n := Subclass.classes ho hn hh hp

theorem defs (_ho : Boot.objectId < m.heap.objs.size)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) {D : DefTable}
    (hp : DefsOk D m) : DefsOk D n := Subclass.defs hh hp

theorem methodsExact (_ho : Boot.objectId < m.heap.objs.size)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e)
    (hp : MethodsExact κ m) : MethodsExact κ n := Subclass.methodsExact hh hp

#print axioms own_code
#print axioms classes
#print axioms defs
#print axioms methodsExact
end Ratchet.Denote.FreshClass
