import Denote.Rules.Expr.Sequence
import Denote.Rules.Primitive.Primitive
import Denote.Rules.Expr.Hash

/-! The context-indexed list companions' constructor obligations. The expression
obligations already live at `SemSafeCtxA.<rule>` beside their interpreter proofs. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open Ratchet

theorem SemSafeCtxA.DJudgePairs.nil {κ : Ctx} {Γ : Env} {I : Ty} :
    SemPairsCtxA κ Γ I [] [] [] κ Γ I := .nil

theorem SemSafeCtxA.DJudgePairs.cons {κ κk κv κ' : Ctx} {Γ Γk Γv Γ' : Env} {I Ik Iv I' σ τ : Ty}
    {k v : Expr} {ps : List (Expr × Expr)} {ks vs : List Ty}
    (hk : SemSafeCtxA κ Γ I k σ κk Γk Ik) (hv : SemSafeCtxA κk Γk Ik v τ κv Γv Iv)
    (hs : SemPairsCtxA κv Γv Iv ps ks vs κ' Γ' I') :
    SemPairsCtxA κ Γ I ((k, v) :: ps) (σ :: ks) (τ :: vs) κ' Γ' I' := .cons hk hv hs

end Ratchet.Denote.Typed
