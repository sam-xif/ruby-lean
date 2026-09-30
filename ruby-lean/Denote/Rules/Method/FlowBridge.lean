import Denote.Bridge.Full
import Denote.Judgment.MethodFlowRules

/-! All alias-aware method premises cross the shared registry. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open Ratchet Ratchet.Denote

theorem dmethodFlow_context {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {facts out : CallbackFacts} {e : Expr} {callback : Bool}
    (h : DMethodFlow κ I fr ps ret Γ facts e τ callback Γ' out) :
    SemMethodFlowBody κ I fr ps ret Γ facts e τ callback Γ' out :=
  dmethodFlow_certified h dsemFam (closed_target dclinks)

#print axioms dmethodFlow_context
end Ratchet.Denote.Typed
