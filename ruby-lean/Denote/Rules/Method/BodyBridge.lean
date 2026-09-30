import Denote.Bridge.Full
import Denote.Judgment.MethodRules

/-! Soundness of callback method bodies through the shared registry. Ordinary premises
are interpreted for every callback code; all method premises are family projections. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open Ratchet Ratchet.Denote

theorem dmethod_context {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {e : Expr} (h : DMethod κ I fr ps ret Γ e τ Γ') :
    SemMethodBody κ I fr ps ret Γ e τ Γ' :=
  dmethod_certified h dsemFam (closed_target dclinks)

#print axioms dmethod_context
end Ratchet.Denote.Typed
