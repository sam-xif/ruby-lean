import Denote.Rules.Instance.InstanceResolve
import Denote.Sem.Names.DispatchName

/-! Actual ordinary dispatch without assuming every instance has an empty payload.
Payload-sensitive names still need that physical premise; other names use a proved guard. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem finishSend_instance_resolved {m : Machine} {o k : ObjId} {name : String} {md : MethodDef}
    {site : SendSite}
    {args : List Value}
    (hp : (m.heap.get o).payload = .none ∨ DirectSendName name)
    (hl : lookup m.heap (.ref o) name = some (k, md)) (hu : md.undefined = false)
    (hc : InstanceMethodCode k name md) (hn : name ≠ "initialize")
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref o))).takeWhile (· != k)) name = none) :
    Interp.finishSend m (.ref o) site name args .none =
      Interp.enterUserMethod m (.ref o) name md args none := by
  rcases hp with hp | hp
  · apply invoke_ordinary_userMethod hp hl hc.builtin hu hc.fromPrelude
    · simp [Interp.visError?, hc.visibility, hn]
    · exact hs
  · apply invoke_direct_userMethod hp hl hc.builtin hu hc.fromPrelude
    · simp [Interp.visError?, hc.visibility, hn]
    · exact hs

theorem finishSend_instance_direct_at {m : Machine} {o k : ObjId} {name : String} {md : MethodDef}
    {site : SendSite} {args : List Value} {rest : List ObjId}
    (hp : (m.heap.get o).payload = .none ∨ DirectSendName name)
    (hl : lookup m.heap (.ref o) name = some (k, md)) (hu : md.undefined = false)
    (hc : InstanceMethodCode k name md) (hn : name ≠ "initialize")
    (ha : ancestors m.heap (classOf m.heap (.ref o)) = k :: rest) :
    Interp.finishSend m (.ref o) site name args .none =
      Interp.enterUserMethod m (.ref o) name md args none :=
  finishSend_instance_resolved hp hl hu hc hn (by simp [ha, Interp.crubyShadow]; rfl)

theorem finishSend_instance_direct {m : Machine} {o k : ObjId} {name : String} {md : MethodDef}
    {args : List Value} {rest : List ObjId}
    (hp : (m.heap.get o).payload = .none ∨ DirectSendName name)
    (hl : lookup m.heap (.ref o) name = some (k, md)) (hu : md.undefined = false)
    (hc : InstanceMethodCode k name md) (hn : name ≠ "initialize")
    (ha : ancestors m.heap (classOf m.heap (.ref o)) = k :: rest) :
    Interp.finishSend m (.ref o) .explicit name args .none =
      Interp.enterUserMethod m (.ref o) name md args none :=
  finishSend_instance_direct_at hp hl hu hc hn ha

#print axioms invoke_direct_userMethod
#print axioms finishSend_instance_resolved
#print axioms finishSend_instance_direct_at
#print axioms finishSend_instance_direct
end Ratchet.Denote.Typed
