import Denote.Rules.Method.MethodState

/-! Caller-side restoration is independent of the instance method's receiver/spine.
Full outgoing conformance still needs scope and dispatch restoration. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem method_pop_selfSpine {κ : Ctx} {Γ : Env} {I : Ty} {m n : Machine}
    {f : RubyCore.Frame} (hm : StateOk κ Γ I m) (ht : FirstOrder I = true)
    (hl : SelfLive m)
    (hc : f.captured = none) (h : Framed (pushMethodFrame m f) n) :
    SelfSpineOk I (popMethodFrame n) κ.scope.closedIvars :=
  (method_pop_framed hm.frameInRange.2 hc h).selfSpine
    (congrArg RubyCore.Frame.self (method_pop_currentFrame hm.frameInRange hc h))
    hl ht hm.selfSpine

#print axioms method_pop_selfSpine
end Ratchet.Denote.Typed
