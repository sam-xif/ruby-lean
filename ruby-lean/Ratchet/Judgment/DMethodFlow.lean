import Ratchet.Judgment.DMethod
import Ratchet.Static.CallbackFacts

/-! Staged callback-alias flow. These constructors are not admission rules until
their source definitions/calls cross the registry and have whole-program coverage. -/
set_option autoImplicit false
namespace Ratchet

mutual
/-- Sorbet 0.6.13405 accepts copying &b, clearing the original, restoring it from
the copy and repeated calls (clinks 240–242); a call after a nil overwrite fails 7003.
Receiver identity is a proved flow fact, separate from its value type and signature. -/
inductive DMethodFlow : Ctx → Ty → Frame → List Ty → Ty → Env → CallbackFacts →
    Expr → Ty → Bool → Env → CallbackFacts → Prop
  | embed {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {facts : CallbackFacts} {e : Expr} :
      DMethod κ I fr ps ret Γ e τ Γ' →
      DMethodFlow κ I fr ps ret Γ facts e τ false Γ' .empty
  | intLit {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret : Ty}
      {Γ : Env} {facts : CallbackFacts} {n : Int} :
      DMethodFlow κ I fr ps ret Γ facts (.int n) .int false Γ facts
  | nilLit {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret : Ty}
      {Γ : Env} {facts : CallbackFacts} :
      DMethodFlow κ I fr ps ret Γ facts .nil .nilT false Γ facts
  | var {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ : Env} {facts : CallbackFacts} {x : String} :
      envGet? Γ x = some τ → isAliasTy τ = false →
      DMethodFlow κ I fr ps ret Γ facts (.var .lvar x) τ (facts.aliases.contains x) Γ facts
  | vasgn {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {facts out : CallbackFacts} {e : Expr} {x : String} {callback : Bool} :
      DMethodFlow κ I fr ps ret Γ facts e τ callback Γ' out →
      capStale x τ τ = false → isAliasTy τ = false →
      (∀ code, capStaleCtx x τ (callbackMethodCtx κ fr code) = false) →
      killClosOverSpine I x τ = I →
      DMethodFlow κ I fr ps ret Γ facts (.vasgn .lvar x e) τ callback (envAfter Γ' x τ)
        (out.write x callback)
  | sequence {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {facts out : CallbackFacts} {es : List Expr} {callback : Bool} :
      DMethodFlowSeq κ I fr ps ret Γ facts es τ callback Γ' out →
      DMethodFlow κ I fr ps ret Γ facts (.seq es) τ callback Γ' out
  | call {κ : Ctx} {I : Ty} {fr : Frame} {σ τ ret : Ty} {Γ Γ₁ Γ₂ : Env}
      {facts mid out : CallbackFacts} {recv arg : Expr} {name : String} {callback : Bool} :
      DMethodFlow κ I fr [σ] ret Γ facts recv τ true Γ₁ mid →
      DMethodFlow κ I fr [σ] ret Γ₁ mid arg σ callback Γ₂ out →
      activationReturnB Γ₂ = true → plainArgB arg = true → nameFreeN κ name = true →
      procCallNameB name = true →
      DMethodFlow κ I fr [σ] ret Γ facts (.send (some recv) name [arg] none) ret false Γ₂ out

/-- Source-order sequencing retains both type and identity updates. -/
inductive DMethodFlowSeq : Ctx → Ty → Frame → List Ty → Ty → Env → CallbackFacts →
    List Expr → Ty → Bool → Env → CallbackFacts → Prop
  | last {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {facts out : CallbackFacts} {e : Expr} {callback : Bool} :
      DMethodFlow κ I fr ps ret Γ facts e τ callback Γ' out →
      DMethodFlowSeq κ I fr ps ret Γ facts [e] τ callback Γ' out
  | cons {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret σ τ : Ty}
      {Γ Γ₁ Γ₂ : Env} {facts mid out : CallbackFacts} {e e' : Expr} {es : List Expr} {c c' : Bool} :
      DMethodFlow κ I fr ps ret Γ facts e σ c Γ₁ mid →
      DMethodFlowSeq κ I fr ps ret Γ₁ mid (e' :: es) τ c' Γ₂ out →
      DMethodFlowSeq κ I fr ps ret Γ facts (e :: e' :: es) τ c' Γ₂ out
end
end Ratchet
