import Denote.Sem.SubclassConstants
import Denote.Sem.ClassFrame

/-! An empty fresh class scope adds no shadowing. The newly registered name is a separate
case; other constants retain both lexical and inherited resolution from the main scope. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine freshModFrame)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem const_self (ho : (h.classPayload? Boot.objectId).isSome = true) :
    constOwn h₁ Boot.objectId name = some (.ref h.objs.size) := Subclass.const_own_self ho

theorem const_own_old_other (_ho : Boot.objectId < h.objs.size) {k : ObjId}
    (hk : k < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constOwn h₁ k cn = constOwn h k cn := Subclass.const_own_old_other hk hn

theorem const_from_eq_firstM (heap : Heap) (k : ObjId) (cn : String) :
    constLookupFrom heap k cn = (ancestors heap k).firstM (fun j => constOwn heap j cn) :=
  Subclass.const_from_eq_firstM heap k cn

theorem const_from_old_other (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    {k : ObjId} (hk : k < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constLookupFrom h₁ k cn = constLookupFrom h k cn := Subclass.const_from_old_other hc hs hk hn

theorem const_from_class_other (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    {cn : String} (hn : cn ≠ name) :
    constLookupFrom h₁ h.objs.size cn = constLookupFrom h Boot.objectId cn :=
  Subclass.const_from_class_other hc hs hc.boot.2.2.2.2 hn

variable {m : Machine} {body : RubyCore.Expr}
local notation "entry" => freshClsMachine m Boot.objectId m.currentFrame.cref name name e body

theorem const_scope (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hcref : m.currentFrame.cref = [Boot.objectId]) (howner : m.currentFrame.defmod = Boot.objectId)
    (hscope : ConstScopeOk m) : ConstScopeOk entry :=
  Subclass.const_scope hc hs ho hc.boot.2.2.2.2 hcref (Subclass.fallback_of_main hcref howner hscope)

#print axioms const_from_class_other
#print axioms const_scope
end Ratchet.Denote.FreshClass
