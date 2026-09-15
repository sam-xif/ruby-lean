import Denote.Sem.ClassDispatch
import Denote.Sem.SubclassQueries
import Denote.Sem.SubclassCore
import Denote.Sem.ClassRootNames

/-! Builtin conformance across fresh class creation: payloads, primitive dispatch/errors,
and core nominal names. No whole-object agreement is assumed for the constant owner. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem primitiveDispatch (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (free : String → Bool) : primitiveDispatchB h₁ free = primitiveDispatchB h free :=
  Subclass.primitiveDispatch hc hs free

theorem primitiveErrors (hc : Proof.ChainsIn h) (hs : Proof.Saturated h) :
    primitiveErrorsB h₁ = primitiveErrorsB h := Subclass.primitiveErrors hc hs

theorem stringPayload (hc : Proof.ChainsIn h) (hp : StringPayloadOk h) : StringPayloadOk h₁ :=
  Subclass.stringPayload hc hp

theorem arrayPayload (hp : ArrayPayloadOk h) : ArrayPayloadOk h₁ := Subclass.arrayPayload hp

theorem hashPayload (hp : HashPayloadOk h) : HashPayloadOk h₁ := Subclass.hashPayload hp

theorem named_live {cn : String} {k : ObjId} (hn : classNamed? h cn = some k) :
    k < h.objs.size := Subclass.named_live hn

theorem core (hc : CoreOk h) (hs : Proof.Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) (he : (h.get Boot.objectId).eigen = some e) :
    CoreOk h₁ := by
  exact Subclass.core hc hs ho hn hc.classReady.chains.boot.2.2.2.2
    (hc.classReady.chains.eigen _ hc.classReady.chains.boot.2.2.2.2 _ he)

#print axioms primitiveDispatch
#print axioms primitiveErrors
#print axioms stringPayload
#print axioms arrayPayload
#print axioms hashPayload
#print axioms core
end Ratchet.Denote.FreshClass
