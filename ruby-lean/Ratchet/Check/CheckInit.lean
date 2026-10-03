import Ratchet.Judgment.InitJudge
import Ratchet.Check.Deriv
import Ratchet.Static.CtxEq

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

/-- Checked at required parameter annotations and the declared return type. The inferred
fields, not initialize's return value, become the later constructed receiver's type. -/
structure CheckedInitializer (κ : Ctx) (decl : Defn) (input : Ty := .ivar0) where
  params : List SigParam
  ret : Ty
  out : Env
  fields : Ty
  paramShape : decl.params = params.map (fun p => Param.req p.1)
  paramsFO : ∀ p ∈ params, FirstOrder p.2 = true ∧ isAliasTy p.2 = false
  returnFO : FirstOrder ret = true
  fieldsFO : FirstOrder fields = true
  judged : InitJudge κ params input decl.body ret κ out fields

/-- Replay metadata from previously annotation-checked definitions. These are hints:
route lookup and a fresh body derivation still justify every use. -/
structure InitializerSource where
  owner : String
  decl : Defn
  params : List SigParam
  ret : Ty
  deriv : Deriv

structure InitCertifiedAll (κ : Ctx) (Γ : Env) (I : Ty) (es : List Expr) where
  tys : List Ty
  ctx : Ctx
  out : Env
  fields : Ty
  judged : InitJudgeAll κ Γ I es tys ctx out fields

mutual
def checkInit (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty) (e : Expr) (d : Deriv) (sources : List InitializerSource := []) :
    Option (InitCertified κ Γ I e) :=
  match fuel with
  | 0 => none
  | n + 1 => match e, d with
    | .int x, .intLit y => if x == y then some ⟨.int, κ, Γ, I, .intLit⟩ else none
    | .super' es none, .superInit ds => checkInitSuper n κ Γ I es ds sources sources
    | .var .lvar x, .var .lvar y => do
        if x != y then none else do
        match hx : envGet? Γ x with
        | none => none
        | some τ => if ha : isAliasTy τ = false then
            some ⟨τ, κ, Γ, I, .var hx ha⟩ else none
    | .vasgn .ivar x e, .ivarAsgn y de => do
        if x != y then none else do
        let c ← checkInit n κ Γ I e de sources
        if hw : writeTypesB c.ctx c.out c.fields x c.ty = true then
          some ⟨c.ty, c.ctx, c.out, ivarSet c.fields x c.ty, .ivarAsgn c.judged hw⟩
        else none
    | .seq es, .seq ds => do
        let c ← checkInitSeq n κ Γ I es ds sources
        some ⟨c.ty, c.ctx, c.out, c.fields, .seq c.judged⟩
    | .str s, .strLit s' => if s == s' then some ⟨.cls "String", κ, Γ, I, .strLit⟩ else none
    | e, .initWiden left σ d => do
        let c ← checkInit n κ Γ I e d sources
        if left then some ⟨joinT c.ty σ, c.ctx, c.out, c.fields, .widenL c.judged⟩
        else some ⟨joinT σ c.ty, c.ctx, c.out, c.fields, .widenR c.judged⟩
    | .if' (.var .lvar x) t (some e), .ifD (.var .lvar y) dt (some de) j => do
        if x != y then none else do
        match hx : envGet? Γ x with
        | none => none
        | some σ =>
          let ct ← checkInit n κ Γ I t dt sources
          let ce ← checkInit n κ Γ I e de sources
          let ⟨hctx⟩ ← ctxEq? ce.ctx ct.ctx
          if hout : ce.out = ct.out then
          if hf : ce.fields = ct.fields then
          if hj : j = joinT ct.ty ce.ty then
            some ⟨j, ct.ctx, ct.out, ct.fields,
              .ifVar hx ct.judged (by rw [← hctx, ← hout, ← hf]; exact ce.judged) hj⟩
          else none
          else none
          else none
    | _, _ => none

def checkInitSeq (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty)
    (es : List Expr) (ds : List Deriv) (sources : List InitializerSource := []) : Option (InitCertifiedSeq κ Γ I es) :=
  match fuel with
  | 0 => none
  | n + 1 => match es, ds with
    | [e], [d] => do
        let c ← checkInit n κ Γ I e d sources
        some ⟨c.ty, c.ctx, c.out, c.fields, .last c.judged⟩
    | e :: e' :: es, d :: ds => do
        let c ← checkInit n κ Γ I e d sources
        let tail ← checkInitSeq n c.ctx c.out c.fields (e' :: es) ds sources
        some ⟨tail.ty, tail.ctx, tail.out, tail.fields, .cons c.judged tail.judged⟩
    | _, _ => none

def checkInitializerBody (fuel : Nat) (κ : Ctx) (decl : Defn) (d : Deriv)
    (sources : List InitializerSource := []) (input : Ty := .ivar0) :
    Option (CheckedInitializer κ decl input) :=
  match fuel with
  | 0 => none
  | n + 1 => match d with
  | .defDecl name ps ret db => do
    if name != decl.name || decl.name != "initialize" then none else do
    if hp : paramEqAll decl.params (ps.map (fun p => Param.req p.1)) = true then do
      if hps : ps.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then do
        if hret : FirstOrder ret = true then do
          let c ← checkInit n κ ps input decl.body db sources
          let ⟨hctx⟩ ← ctxEq? c.ctx κ
          if hfields : FirstOrder c.fields = true then do
            let finish (hj : InitJudge κ ps input decl.body ret κ c.out c.fields) :=
              some (show CheckedInitializer κ decl input from
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

def checkInitAll (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty) (es : List Expr)
    (ds : List Deriv) (sources : List InitializerSource) : Option (InitCertifiedAll κ Γ I es) :=
  match fuel with
  | 0 => none
  | n + 1 => match es, ds with
    | [], [] => some ⟨[], κ, Γ, I, .nil⟩
    | e :: es, d :: ds => do
      if hp : plainArgB e = true then do
        let c ← checkInit n κ Γ I e d sources
        if ht : IvarStable c.ty = true then do
          let tail ← checkInitAll n c.ctx c.out c.fields es ds sources
          some ⟨c.ty :: tail.tys, tail.ctx, tail.out, tail.fields, .cons c.judged tail.judged hp ht⟩
        else none
      else none
    | _, _ => none

def checkInitSuper (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty) (es : List Expr) (ds : List Deriv)
    (sources candidates : List InitializerSource) : Option (InitCertified κ Γ I (.super' es none)) :=
  match fuel with
  | 0 => none
  | n + 1 => match candidates with
    | [] => none
    | src :: rest =>
      let attempt : Option (InitCertified κ Γ I (.super' es none)) := do
        let fr ← κ.frame
        let c ← findClass fr.recvClass κ.classes
        let route ← superRoute? κ.classes c.cls.name fr.defClass src.owner src.decl
        let a ← checkInitAll n κ Γ I es ds sources
        let ⟨hctx⟩ ← ctxEq? a.ctx κ
        let body ← checkInitializerBody n (initializerBodyCtxAt κ c.cls.name src.owner)
          src.decl (.defDecl src.decl.name src.params src.ret src.deriv) sources a.fields
        if htys : a.tys = body.params.map (·.2) then do
          if hg : superInitB κ a.out a.fields body.fields c.cls fr.defClass src.decl body.params body.ret = true then
            some ⟨body.ret, κ, a.out, body.fields,
              .superInit (by simpa only [hctx, htys] using a.judged) body.judged c.member route hg⟩
          else none
        else none
      attempt.orElse (fun _ => checkInitSuper n κ Γ I es ds sources rest)
end

/-- Recheck in a new context without trusting a replay hint to replace the checked
annotations. This produces a new proof; it never casts the earlier body's context. -/
def refreshInitializerBody {κ : Ctx} {decl : Defn} (fuel : Nat) (κ' : Ctx)
    (c : CheckedInitializer κ decl) (bodyHint : Deriv)
    (sources : List InitializerSource := []) : Option (CheckedInitializer κ' decl) :=
  checkInitializerBody fuel κ' decl (.defDecl decl.name c.params c.ret bodyHint) sources

end Ratchet
