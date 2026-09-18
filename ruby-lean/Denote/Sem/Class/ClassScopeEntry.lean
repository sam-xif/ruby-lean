import Denote.Sem.Subclass.SubclassSites
import Denote.Sem.Class.ClassFrame
import Denote.Sem.Class.ClassDispatch

/-! Establish the requested scope at the actual fresh-class transition. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine freshModFrame)

variable {m : Machine} {cn : String} {e : ObjId} {body : RubyCore.Expr}
local notation "entry" => freshClsMachine m Boot.objectId m.currentFrame.cref cn cn e body

theorem hook_quiet (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hh : objectHookQuietB m.heap = true) :
    definitionHookQuietB (entry).heap m.heap.objs.size = true :=
  Subclass.hook_quiet hc hs hc.boot.2.2.2.2 he hh

theorem scope_ready (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hm : MainReady m) :
    ClassScopeReady cn entry :=
  Subclass.scope_ready hc hs hm.classLive hc.boot.2.2.2.2 he hm.hook hm.cref hm.phase

#print axioms scope_ready
end Ratchet.Denote.FreshClass
