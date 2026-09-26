import Denote.Bridge
import Denote.Judgment.MethodRules

/-! Soundness of the staged method-body judgment. Ordinary premises cross the existing
registry for every callback code. The method families must join DFam before a registered
whole-program rule may consume them; Registry rejects any raw use in the meantime. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open Ratchet Ratchet.Denote

theorem dmethod_context {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {e : Expr} (h : DMethod κ I fr ps ret Γ e τ Γ') :
    SemMethodBody κ I fr ps ret Γ e τ Γ' := by
  refine DMethod.rec
    (motive_1 := fun ps ret Γ e τ Γ' _ => SemMethodBody κ I fr ps ret Γ e τ Γ')
    (motive_2 := fun ps ret Γ es tys Γ' _ => SemMethodBodyAll κ I fr ps ret Γ es tys Γ')
    (motive_3 := fun ps ret Γ es τ Γ' _ => SemMethodBodySeq κ I fr ps ret Γ es τ Γ')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals intros
  · rename_i ps ret τ Γ Γ' e ordinary
    exact SemSafeCtxA.DMethod.ordinary (fun code => djudge_context (ordinary code))
  · apply SemSafeCtxA.DMethod.vasgn <;> assumption
  · apply SemSafeCtxA.DMethod.sequence <;> assumption
  · apply SemSafeCtxA.DMethod.prim <;> assumption
  · apply SemSafeCtxA.DMethod.yieldOne <;> assumption
  · exact SemSafeCtxA.DMethodAll.nil
  · apply SemSafeCtxA.DMethodAll.cons <;> assumption
  · apply SemSafeCtxA.DMethodSeq.last <;> assumption
  · apply SemSafeCtxA.DMethodSeq.cons <;> assumption

#print axioms dmethod_context
end Ratchet.Denote.Typed
