import Denote.Rules.Expr.Sequence
import Denote.Rules.Primitive.Primitive
import Denote.Rules.Expr.Hash

/-! The context-indexed list companions' constructor obligations. The expression
obligations already live at `SemSafeCtxA.<rule>` beside their interpreter proofs. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open Ratchet

theorem SemSafeCtxA.DJudgeAll.nil {κ : Ctx} {Γ : Env} {I : Ty} :
    SemAllCtxA κ Γ I [] [] κ Γ I := .nil

theorem SemSafeCtxA.DJudgeAll.cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ τ : Ty}
    {e : Expr} {es : List Expr} {tys : List Ty}
    (he : SemSafeCtxA κ Γ I e τ κ₁ Γ₁ I₁) (ht : SemAllCtxA κ₁ Γ₁ I₁ es tys κ₂ Γ₂ I₂)
    (hp : plainArgB e = true) : SemAllCtxA κ Γ I (e :: es) (τ :: tys) κ₂ Γ₂ I₂ := .cons he ht hp

theorem SemSafeCtxA.DJudgeSeq.last {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Expr}
    (he : SemSafeCtxA κ Γ I e τ κ' Γ' I') : SemSeqCtxA κ Γ I [e] τ κ' Γ' I' := .last he

theorem SemSafeCtxA.DJudgeSeq.cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
    {e e' : Expr} {es : List Expr} (he : SemSafeCtxA κ Γ I e σ κ₁ Γ₁ I₁)
    (ht : SemSeqCtxA κ₁ Γ₁ I₁ (e' :: es) τ κ₂ Γ₂ I₂) :
    SemSeqCtxA κ Γ I (e :: e' :: es) τ κ₂ Γ₂ I₂ := .cons he ht

theorem SemSafeCtxA.DJudgePairs.nil {κ : Ctx} {Γ : Env} {I : Ty} :
    SemPairsCtxA κ Γ I [] [] [] κ Γ I := .nil

theorem SemSafeCtxA.DJudgePairs.cons {κ κk κv κ' : Ctx} {Γ Γk Γv Γ' : Env} {I Ik Iv I' σ τ : Ty}
    {k v : Expr} {ps : List (Expr × Expr)} {ks vs : List Ty}
    (hk : SemSafeCtxA κ Γ I k σ κk Γk Ik) (hv : SemSafeCtxA κk Γk Ik v τ κv Γv Iv)
    (hs : SemPairsCtxA κv Γv Iv ps ks vs κ' Γ' I') :
    SemPairsCtxA κ Γ I ((k, v) :: ps) (σ :: ks) (τ :: vs) κ' Γ' I' := .cons hk hv hs

end Ratchet.Denote.Typed
