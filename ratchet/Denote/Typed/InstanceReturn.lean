import Denote.Typed.MethodChecked

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

/-- An annotation-checked body supplies framing and its declared answer type. This
restores caller fields, not yet all caller conformance or a full dispatched-call contract. -/
theorem checked_body_pop_fields {κ κb : Ctx} {Γ : Env} {I Ib : Ty} {m n : Machine}
    {f : RubyCore.Frame} {decl : Defn} {fuel rest : Nat} {v : Value}
    (body : CheckedBody κb Ib decl) (hm : StateOk κ Γ I m)
    (ht : FirstOrder I = true) (hl : SelfLive m) (hc : f.captured = none)
    (he : StateOk κb body.params Ib (pushMethodFrame m f))
    (hr : runA fuel (evalFrom (pushMethodFrame m f) decl.body) = .ans (.val v) n rest) :
    denM body.ret (popMethodFrame n) v ∧
      SelfSpineOk I (popMethodFrame n) κ.scope.closedIvars := by
  have result := (checked_body_context body _ he).2 fuel (.val v) n rest hr
  exact ⟨(denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) body.returnFO rfl).mp result.2.1,
    method_pop_selfSpine hm ht hl hc result.1⟩

#print axioms method_pop_selfSpine
#print axioms checked_body_pop_fields
end Ratchet.Denote.Typed
