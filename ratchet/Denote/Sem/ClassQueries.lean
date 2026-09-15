import Denote.Sem.ClassDispatch
import Denote.Sem.SubclassQueries

/-! Query invariants across fresh class creation. Method lookup alone is insufficient:
native-name shadows and the new class-object receiver sites must also be covered. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem class_site_parent (hc : Proof.ChainsIn h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (he : (h.get Boot.objectId).eigen = some e) {k : ObjId}
    (hk : ClassQuerySite h₁ k) : ClassQuerySite h (parent h e k) := Subclass.class_site_source hc ho he hk

variable {κ : Ctx} {m n : Machine}

theorem query (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (he : e < m.heap.objs.size) (hne : name.isEmpty = false)
    (hn : ∀ mn bid, (mn, bid) ∈ queryBuiltins → nameFreeN κ mn = true → NativeQuiet name mn)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) (hq : QueryOk κ m) :
    QueryOk κ n := Subclass.query hc hs hc.boot.2.2.2.2 he hne hn hh hq

theorem clsQuery (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hne : name.isEmpty = false)
    (hn : ∀ mn bid, (mn, bid) ∈ clsQueryBuiltins → nameFreeN κ mn = true → NativeQuiet name mn)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) (hq : ClsQueryOk κ m) :
    ClsQueryOk κ n := Subclass.clsQuery hc hs ho he hne hn hh hq

theorem nilQuery (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (he : e < m.heap.objs.size) (hne : name.isEmpty = false)
    (hn : nameFreeN κ "nil?" = true → NativeQuiet name "nil?")
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e) (hq : NilQueryOk κ m) :
    NilQueryOk κ n := Subclass.nilQuery hc hs hc.boot.2.2.2.2 he hne hn hh hq

#print axioms class_site_parent
#print axioms query
#print axioms clsQuery
#print axioms nilQuery
end Ratchet.Denote.FreshClass
