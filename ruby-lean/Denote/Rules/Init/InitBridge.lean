import Denote.Clink.Registry

/-! Both initializer families cross the registry; a raw body derivation cannot bypass it. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open Ratchet

theorem initJudge_certified {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr}
    (h : InitJudge κ Γ I e τ κ' Γ' I') :
    (DJudgeC dclinks).init κ Γ I e τ κ' Γ' I' := by
  intro F hF
  refine InitJudge.rec
    (motive_1 := fun κ Γ I e τ κ' Γ' I' _ => F.init κ Γ I e τ κ' Γ' I')
    (motive_2 := fun κ Γ I es τ κ' Γ' I' _ => F.initSeq κ Γ I es τ κ' Γ' I')
    ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; apply hF DClink.InitJudge.var (by simp [dclinks]) <;> assumption
  · intros; apply hF DClink.InitJudge.ivarAsgn (by simp [dclinks]) <;> assumption
  · intros; apply hF DClink.InitJudge.seq (by simp [dclinks]) <;> assumption
  · intros; apply hF DClink.InitJudge.ignoreResult (by simp [dclinks]) <;> assumption
  · intros; apply hF DClink.InitJudgeSeq.last (by simp [dclinks]) <;> assumption
  · intros; apply hF DClink.InitJudgeSeq.cons (by simp [dclinks]) <;> assumption

#print axioms initJudge_certified
end Ratchet.Denote.Typed
