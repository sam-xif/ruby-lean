import Ratchet.InitJudge
import Ratchet.Deriv
import Ratchet.CtxEq

/-! Initializer-body certificates are checked against the program and annotations, with
no caller values or locals. The output field shape is inferred from proved writes. This
artifact is consumed by the whole-program checker's definition and constructor rules. -/
set_option autoImplicit false
namespace Ratchet

structure InitCertified (κ : Ctx) (Γ : Env) (I : Ty) (e : Expr) where
  ty : Ty
  ctx : Ctx
  out : Env
  fields : Ty
  judged : InitJudge κ Γ I e ty ctx out fields

structure InitCertifiedSeq (κ : Ctx) (Γ : Env) (I : Ty) (es : List Expr) where
  ty : Ty
  ctx : Ctx
  out : Env
  fields : Ty
  judged : InitJudgeSeq κ Γ I es ty ctx out fields

mutual
def checkInit (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty) (e : Expr) (d : Deriv) :
    Option (InitCertified κ Γ I e) :=
  match fuel with
  | 0 => none
  | n + 1 => match e, d with
    | .var .lvar x, .var .lvar y => do
        if x != y then none else do
        match hx : envGet? Γ x with
        | none => none
        | some τ => if ha : isAliasTy τ = false then
            some ⟨τ, κ, Γ, I, .var hx ha⟩ else none
    | .vasgn .ivar x e, .ivarAsgn y de => do
        if x != y then none else do
        let c ← checkInit n κ Γ I e de
        if hw : writeTypesB c.ctx c.out c.fields x c.ty = true then
          some ⟨c.ty, c.ctx, c.out, ivarSet c.fields x c.ty, .ivarAsgn c.judged hw⟩
        else none
    | .seq es, .seq ds => do
        let c ← checkInitSeq n κ Γ I es ds
        some ⟨c.ty, c.ctx, c.out, c.fields, .seq c.judged⟩
    | _, _ => none

def checkInitSeq (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty)
    (es : List Expr) (ds : List Deriv) : Option (InitCertifiedSeq κ Γ I es) :=
  match fuel with
  | 0 => none
  | n + 1 => match es, ds with
    | [e], [d] => do
        let c ← checkInit n κ Γ I e d
        some ⟨c.ty, c.ctx, c.out, c.fields, .last c.judged⟩
    | e :: e' :: es, d :: ds => do
        let c ← checkInit n κ Γ I e d
        let tail ← checkInitSeq n c.ctx c.out c.fields (e' :: es) ds
        some ⟨tail.ty, tail.ctx, tail.out, tail.fields, .cons c.judged tail.judged⟩
    | _, _ => none
end

/-- Checked at required parameter annotations and the declared return type. The inferred
fields, not initialize's return value, become the later constructed receiver's type. -/
structure CheckedInitializer (κ : Ctx) (decl : Defn) where
  params : List SigParam
  ret : Ty
  out : Env
  fields : Ty
  paramShape : decl.params = params.map (fun p => Param.req p.1)
  paramsFO : ∀ p ∈ params, FirstOrder p.2 = true ∧ isAliasTy p.2 = false
  returnFO : FirstOrder ret = true
  fieldsFO : FirstOrder fields = true
  judged : InitJudge κ params .ivar0 decl.body ret κ out fields

def checkInitializerBody (fuel : Nat) (κ : Ctx) (decl : Defn) (d : Deriv) :
    Option (CheckedInitializer κ decl) :=
  match fuel with
  | 0 => none
  | n + 1 => match d with
  | .defDecl name ps ret db => do
    if name != decl.name || decl.name != "initialize" then none else do
    if hp : paramEqAll decl.params (ps.map (fun p => Param.req p.1)) = true then do
      if hps : ps.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then do
        if hret : FirstOrder ret = true then do
          let c ← checkInit n κ ps .ivar0 decl.body db
          let ⟨hctx⟩ ← ctxEq? c.ctx κ
          if hfields : FirstOrder c.fields = true then do
            let finish (hj : InitJudge κ ps .ivar0 decl.body ret κ c.out c.fields) :=
              some (show CheckedInitializer κ decl from
                ⟨ps, ret, c.out, c.fields, paramEqAll_sound hp,
                 by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using hps,
                 hret, hfields, hj⟩)
            if hr : c.ty = ret then
              finish (by simpa only [hctx, hr] using c.judged)
            else if ha : ret = .any then
              finish (by simpa only [hctx, ha] using InitJudge.ignoreResult c.judged)
            else none
          else none
        else none
      else none
    else none
  | _ => none

/-- Recheck in a new context without trusting a replay hint to replace the checked
annotations. This produces a new proof; it never casts the earlier body's context. -/
def refreshInitializerBody {κ : Ctx} {decl : Defn} (fuel : Nat) (κ' : Ctx)
    (c : CheckedInitializer κ decl) (bodyHint : Deriv) : Option (CheckedInitializer κ' decl) :=
  checkInitializerBody fuel κ' decl (.defDecl decl.name c.params c.ret bodyHint)

end Ratchet
