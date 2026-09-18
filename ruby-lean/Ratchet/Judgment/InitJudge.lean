import Ratchet.Guards.WriteTypes

/-! Scoped initializer derivations: the fresh receiver's field shape may change. This is
distinct from ordinary preservation; the registry carries both initializer families.
No class, annotation, arity, or field name is fixed by these rules. -/
set_option autoImplicit false
namespace Ratchet

mutual
inductive InitJudge : Ctx → Env → Ty → Expr → Ty → Ctx → Env → Ty → Prop
  | var {κ : Ctx} {Γ : Env} {I τ : Ty} {x : String} :
      envGet? Γ x = some τ → isAliasTy τ = false →
      InitJudge κ Γ I (.var .lvar x) τ κ Γ I
  | ivarAsgn {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {x : String} {e : Expr} :
      InitJudge κ Γ I e τ κ' Γ' I' → writeTypesB κ' Γ' I' x τ = true →
      InitJudge κ Γ I (.vasgn .ivar x e) τ κ' Γ' (ivarSet I' x τ)
  | seq {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {es : List Expr} :
      InitJudgeSeq κ Γ I es τ κ' Γ' I' → InitJudge κ Γ I (.seq es) τ κ' Γ' I'
  /-- Forget only the value type (void/untyped return), never the body or its effects. -/
  | ignoreResult {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Expr} :
      InitJudge κ Γ I e τ κ' Γ' I' → InitJudge κ Γ I e .any κ' Γ' I'

inductive InitJudgeSeq : Ctx → Env → Ty → List Expr → Ty → Ctx → Env → Ty → Prop
  | last {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Expr} :
      InitJudge κ Γ I e τ κ' Γ' I' → InitJudgeSeq κ Γ I [e] τ κ' Γ' I'
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
      {e e' : Expr} {es : List Expr} :
      InitJudge κ Γ I e σ κ₁ Γ₁ I₁ → InitJudgeSeq κ₁ Γ₁ I₁ (e' :: es) τ κ₂ Γ₂ I₂ →
      InitJudgeSeq κ Γ I (e :: e' :: es) τ κ₂ Γ₂ I₂
end

end Ratchet
