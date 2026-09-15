import Denote.Sem.SubclassDeclared
import Denote.Sem.OwnNames
import Denote.Sem.ClassMethods

/-! Own-selector bounds survive fresh class creation, and its actually empty table
establishes the new header's bound. All class names and existing class tables are arbitrary. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

theorem ownNames {C : CTable} {m : Machine} {name : String} {e : ObjId}
    (ho : Boot.objectId < m.heap.objs.size) (hn : constOwn m.heap Boot.objectId name = none)
    (hc : ClassesOk C m) (hp : ClassOwnNames C m.heap) :
    ClassOwnNames C (freshClsHeap m.heap Boot.objectId name name e) :=
  Subclass.ownNames ho hn hc hp

theorem ownNames_header {C : CTable} {m : Machine} {name : String} {e : ObjId}
    (ho : Boot.objectId < m.heap.objs.size)
    (hc : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (ht : ClassesOk C m) (hp : ClassOwnNames C m.heap) :
    ClassOwnNames (classHeader name :: C) (freshClsHeap m.heap Boot.objectId name name e) := by
  apply (ownNames ho hn ht hp).cons_empty
  intro k hk
  have he := (classNamed_freshClass (name := name) (e := e) hc ho).symm.trans hk
  have heq := Option.some.inj he
  subst k
  rw [ownMethods, Proof.Judgment.freshClsHeap_cp_k]
  rfl

#print axioms ownNames_header
end Ratchet.Denote.FreshClass
