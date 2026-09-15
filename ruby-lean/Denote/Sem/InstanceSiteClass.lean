import Denote.Sem.SubclassSites
import Denote.Sem.InstanceSite
import Denote.Sem.ClassConstants
import Denote.Sem.ClassCore
import Denote.Sem.MetaReadyClass

/-! A fresh top-level class preserves existing instance-call sites. The newly bound
constant is handled separately: absence is not stable, but lexical/global agreement is. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem classFront_old (_ho : Boot.objectId < h.objs.size) {k : ObjId}
    (hk : k < h.objs.size) : classFrontB h₁ k = classFrontB h k := Subclass.classFront_old hk

theorem instance_constants_old {κ : Ctx} {cn : String} {k : ObjId}
    (site : InstanceSite κ cn k h) (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) :
    ∀ n, instanceConstResolve h₁ k n = constLookup h₁ n :=
  Subclass.instance_constants_old site hc hs ho hn

theorem instanceSite_old {κ : Ctx} {cn : String} {k : ObjId}
    (site : InstanceSite κ cn k h) (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) : InstanceSite κ cn k h₁ :=
  Subclass.instanceSite_old site hc hs ho hn

#print axioms instance_constants_old
#print axioms instanceSite_old
end Ratchet.Denote.FreshClass
