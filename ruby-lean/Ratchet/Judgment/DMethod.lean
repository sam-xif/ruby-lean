import Ratchet.Judgment.DJudge
import Ratchet.Guards.Callback

/-! Method bodies are checked against block argument/result types, independently of
the eventual callback's code, local names or captured environment. -/
set_option autoImplicit false
namespace Ratchet

mutual
/-- Sorbet 0.6.13405 checks `yield(1)+yield(2)` against the declared
`T.proc.params(x: Integer).returns(Integer)`, including in uncalled definitions;
it rejects a String operand (7002). Clinks 234–236 also measure local retyping and
nested yields. Ordinary premises must work for every callback code, not one caller. -/
inductive DMethod : Ctx → Ty → Frame → List Ty → Ty → Env → Expr → Ty → Env → Prop
  | ordinary {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {e : Expr} :
      (∀ code, DJudge Γ e τ Γ' (callbackMethodCtx κ fr code) I (callbackMethodCtx κ fr code) I) →
      DMethod κ I fr ps ret Γ e τ Γ'
  | vasgn {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {e : Expr} {x : String} :
      DMethod κ I fr ps ret Γ e τ Γ' → capStale x τ τ = false → isAliasTy τ = false →
      (∀ code, capStaleCtx x τ (callbackMethodCtx κ fr code) = false) →
      killClosOverSpine I x τ = I →
      DMethod κ I fr ps ret Γ (.vasgn .lvar x e) τ (envAfter Γ' x τ)
  | sequence {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {es : List Expr} :
      DMethodSeq κ I fr ps ret Γ es τ Γ' → DMethod κ I fr ps ret Γ (.seq es) τ Γ'
  | prim {κ : Ctx} {I : Ty} {fr : Frame} {ps tys : List Ty} {ret σ τ : Ty}
      {Γ Γ₁ Γ₂ : Env} {recv : Expr} {name : String} {args : List Expr} :
      DMethod κ I fr ps ret Γ recv σ Γ₁ → DMethodAll κ I fr ps ret Γ₁ args tys Γ₂ →
      DPrim σ name tys τ → nameFreeN κ name = true →
      (σ = .cls "String" → isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) →
      DMethod κ I fr ps ret Γ (.send (some recv) name args none) τ Γ₂
  | yieldOne {κ : Ctx} {I : Ty} {fr : Frame} {σ ret : Ty} {Γ Γ' : Env} {arg : Expr} :
      DMethod κ I fr [σ] ret Γ arg σ Γ' → activationReturnB Γ' = true → plainArgB arg = true →
      DMethod κ I fr [σ] ret Γ (.yield' [arg]) ret Γ'

/-- Source-order argument typing, with the same Sorbet block signature throughout. -/
inductive DMethodAll : Ctx → Ty → Frame → List Ty → Ty → Env → List Expr → List Ty → Env → Prop
  | nil {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret : Ty} {Γ : Env} :
      DMethodAll κ I fr ps ret Γ [] [] Γ
  | cons {κ : Ctx} {I : Ty} {fr : Frame} {ps tys : List Ty} {ret τ : Ty}
      {Γ Γ₁ Γ₂ : Env} {e : Expr} {es : List Expr} :
      DMethod κ I fr ps ret Γ e τ Γ₁ → DMethodAll κ I fr ps ret Γ₁ es tys Γ₂ →
      plainArgB e = true → DMethodAll κ I fr ps ret Γ (e :: es) (τ :: tys) Γ₂

/-- Flat sequences retain the method's outgoing locals between yields (Sorbet, clink 234). -/
inductive DMethodSeq : Ctx → Ty → Frame → List Ty → Ty → Env → List Expr → Ty → Env → Prop
  | last {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {e : Expr} :
      DMethod κ I fr ps ret Γ e τ Γ' → DMethodSeq κ I fr ps ret Γ [e] τ Γ'
  | cons {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret σ τ : Ty}
      {Γ Γ₁ Γ₂ : Env} {e e' : Expr} {es : List Expr} :
      DMethod κ I fr ps ret Γ e σ Γ₁ → DMethodSeq κ I fr ps ret Γ₁ (e' :: es) τ Γ₂ →
      DMethodSeq κ I fr ps ret Γ (e :: e' :: es) τ Γ₂
end

end Ratchet
