import Books.TypeSoundness.Soundness.Full
import Books.TypeSoundness.Judgment.MethodRules

/-! Soundness of callback method bodies through the shared registry. Ordinary premises
are interpreted for every callback code; all method premises are family projections. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open Checker Checker.Soundness

theorem dmethod_context {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {e : Expr} (h : DMethod κ I fr ps ret Γ e τ Γ') :
    SemMethodBody κ I fr ps ret Γ e τ Γ' :=
  dmethod_certified h dsemFam (closed_target dclinks)

#print axioms dmethod_context
end Checker.Soundness.Typed
