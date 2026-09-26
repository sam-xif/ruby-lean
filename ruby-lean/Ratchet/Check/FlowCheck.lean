import Ratchet.Check.Certified
import Ratchet.Check.CallbackCache

/-! Proof-producing local-flow checking. The ordinary checker is a callback at
strictly smaller fuel, including when the stored body is larger than the call. -/
set_option autoImplicit false
namespace Ratchet

structure CertifiedFlow (κ : Ctx) (Γ : Env) (I : Ty) (incoming : LocalFacts) (e : Expr) where
  ty : Ty
  current : Bool
  ctx : Ctx
  out : Env
  spine : Ty
  facts : LocalFacts
  judged : DFlow κ Γ I incoming e ty current ctx out spine facts
  cache : CheckedCache := {}

structure CertifiedFlowSeq (κ : Ctx) (Γ : Env) (I : Ty) (incoming : LocalFacts) (es : List Expr) where
  ty : Ty
  current : Bool
  ctx : Ctx
  out : Env
  spine : Ty
  facts : LocalFacts
  judged : DFlowSeq κ Γ I incoming es ty current ctx out spine facts
  cache : CheckedCache := {}

abbrev OrdinaryCheck := (Γ : Env) → (e : Expr) → Deriv → (κ : Ctx) → (I : Ty) →
  CheckedCache → Option (Certified Γ e κ I)

structure CertifiedFlowAll (κ : Ctx) (Γ : Env) (I : Ty) (incoming : LocalFacts) (es : List Expr) where
  tys : List Ty
  ctx : Ctx
  out : Env
  spine : Ty
  facts : LocalFacts
  judged : DFlowAll κ Γ I incoming es tys ctx out spine facts
  cache : CheckedCache := {}

/-- Bind exactly the checked argument types to source-required names. No hint supplies
parameter types, and missing/extra arguments cannot yield a certified parameter list. -/
def requiredFlowParams? (ps : List Param) (ts : List Ty) :
    Option {qs : List SigParam // ps = qs.map (fun p => Param.req p.1) ∧ ts = qs.map (·.2)} :=
  match ps, ts with
  | [], [] => some ⟨[], rfl, rfl⟩
  | .req x :: ps, t :: ts => do
    let ⟨qs, hp, ht⟩ ← requiredFlowParams? ps ts
    some ⟨(x, t) :: qs, by simp only [List.map_cons, hp], by simp only [List.map_cons, ht]⟩
  | _, _ => none

mutual
def checkFlow (fuel : Nat) (ordinary : OrdinaryCheck) (κ : Ctx) (Γ : Env) (I : Ty)
    (facts : LocalFacts) (e : Expr) (d : Deriv) (cache : CheckedCache) :
    Option (CertifiedFlow κ Γ I facts e) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match e, d with
    | .int k, .intLit k' =>
      if k == k' then some ⟨.int, false, κ, Γ, I, facts, .intLit facts k, cache⟩ else none
    | .nil, .nilLit => some ⟨.nilT, false, κ, Γ, I, facts, .nilLit facts, cache⟩
    | .var .lvar x, .var .lvar y => do
      if x != y then none else do
      match hx : envGet? Γ x with
      | none => none
      | some τ =>
        if ha : isAliasTy τ = false then
          some ⟨τ, facts.currentProcs.contains x, κ, Γ, I, facts, .var facts hx ha, cache⟩
        else none
    | .send none name [] (some (.block ps ls body)), .closureLiteral => do
      let lam ← if name == "lambda" then some true else if name == "proc" then some false else none
      if hn : name = (if lam then "lambda" else "proc") then do
      if hs : (paramEqAll ps ps && exprEq body body) = true then do
      let code : ClosureCode := ⟨ps, ls, body, lam, hs⟩
      if hf : nameFreeN κ (if lam then "lambda" else "proc") = true then
        some ⟨.clos code .ivar0 .never, true, κ, Γ, I, facts,
          by simpa only [hn] using DFlow.closureLiteral (κ := κ) (Γ := Γ) (I := I) facts code hf, cache⟩
      else none
      else none
      else none
    | .vasgn .lvar x e, .vasgn .lvar y d => do
      if x != y then none else do
      let c ← checkFlow n ordinary κ Γ I facts e d cache
      if hc : capStale x c.ty c.ty = false then do
      if ha : isAliasTy c.ty = false then do
      if hk : capStaleCtx x c.ty c.ctx = false then do
      if hm : c.ctx.scope.runtimeMain = true then
        some ⟨c.ty, c.current, c.ctx, envAfter c.out x c.ty, killClosOverSpine c.spine x c.ty,
          c.facts.write x c.current, .vasgn c.judged hc ha hk hm, c.cache⟩
      else none
      else none
      else none
      else none
    | .seq es, .seq ds => do
      let c ← checkFlowSeq n ordinary κ Γ I facts es ds cache
      some ⟨c.ty, c.current, c.ctx, c.out, c.spine, c.facts, .sequence c.judged, c.cache⟩
    | .send (some (.var .lvar name)) "call" [] none, .closureCall body ret => do
      match hv : envGet? Γ name with
      | some (.clos code cap selfT) => do
        if hc : closureMainB κ I = true then do
        if ha : activationEnvB Γ = true then do
        if ht : FirstOrder ret = true then do
        if hx : name ∈ facts.currentProcs then do
        if hf : nameFreeN κ "call" = true then do
        if hp : code.params.isEmpty = true then do
        if hl : code.locals = [] then do
        if hm : code.lam = true then do
          let c ← ordinary Γ code.body body (closureBodyCtx κ) I cache
          if hr : c.ty = ret then do
          let ⟨hκ⟩ ← ctxEq? c.ctx (closureBodyCtx κ)
          if hi : c.spine = I then do
          if hb : activationEnvB c.out = true then do
          match hn : facts.captureNames? c.out with
          | none => none
          | some names =>
            some ⟨ret, false, κ, captureEnv names c.out, I, .unknown,
              .call name hc ha hb ht hn hx hv hf (List.isEmpty_iff.mp hp) hl hm
                (by simpa only [hr, hκ, hi] using c.judged), cache⟩
          else none
          else none
          else none
        else none
        else none
        else none
        else none
        else none
        else none
        else none
        else none
      | _ => none
    | .send (some recv) name args none, .requiredClosureCall dr ds body ret => do
      let r ← checkFlow n ordinary κ Γ I facts recv dr cache
      match hty : r.ty with
      | .clos code cap selfT => do
        if hc : r.current = true then do
        let a ← checkFlowAll n ordinary r.ctx r.out r.spine r.facts args ds r.cache
        let ⟨ps, hp, hts⟩ ← requiredFlowParams? code.params a.tys
        if hat : a.tys.all FirstOrder = true then do
        if hm : closureMainB a.ctx a.spine = true then do
        if hfree : nameFreeN a.ctx name = true then do
        if hname : procCallNameB name = true then do
        if hin : activationEnvB (ps ++ blockLocals code.locals ++ a.out) = true then do
        if hret : FirstOrder ret = true then do
        let b ← ordinary (ps ++ blockLocals code.locals ++ a.out) code.body body
          (closureBodyCtx a.ctx) a.spine a.cache
        if hbty : b.ty = ret then do
        let ⟨hbctx⟩ ← ctxEq? b.ctx (closureBodyCtx a.ctx)
        if hbspine : b.spine = a.spine then do
        if hout : activationReturnB b.out = true then do
        match hn : a.facts.captureNames? (withoutNames (ps.map (·.1) ++ code.locals) b.out) with
        | none => none
        | some names =>
          some ⟨ret, false, a.ctx, closureReturnEnv (ps.map (·.1) ++ code.locals) names a.out b.out,
            a.spine, .unknown, .requiredCall
              (by simpa only [hty, hc] using r.judged)
              (by simpa only [hts] using a.judged)
              (by simpa only [hts] using List.all_eq_true.mp hat)
              hm hfree hp hname hin hout hret hn
              (by simpa only [hbty, hbctx, hbspine] using b.judged), b.cache⟩
        else none
        else none
        else none
        else none
        else none
        else none
        else none
        else none
        else none
        else none
      | _ => none
    | .send (some recv) "each" [] (some (.block [.req name] locals body)), .eachBlock dr db => do
      let r ← checkFlow n ordinary κ Γ I facts recv dr cache
      match hty : r.ty with
      | .arrayOf σ => do
        if hf : nameFreeN r.ctx "each" = true then do
        if hm : closureMainB r.ctx r.spine = true then do
        if hσ : FirstOrder σ = true then do
        if hin : activationEnvB ([(name, σ)] ++ blockLocals locals ++ r.out) = true then do
        let b ← ordinary ([(name, σ)] ++ blockLocals locals ++ r.out) body db
          (closureBodyCtx r.ctx) r.spine r.cache
        let ⟨hbctx⟩ ← ctxEq? b.ctx (closureBodyCtx r.ctx)
        if hbspine : b.spine = r.spine then do
        if hout : activationReturnB b.out = true then do
        match hn : r.facts.captureNames? (withoutNames ([name] ++ locals) b.out) with
        | none => none
        | some names =>
          if hfix : closureReturnEnv ([name] ++ locals) names r.out b.out = r.out then
            some ⟨.arrayOf σ, false, r.ctx, r.out, r.spine, .unknown,
              .each (by simpa only [hty] using r.judged) hf hm hσ hn hin hout hfix
                (by simpa only [hbctx, hbspine] using b.judged), b.cache⟩
          else none
        else none
        else none
        else none
        else none
        else none
        else none
      | _ => none
    | .send (some recv) mname [] (some (.block [.req name] locals body)), .mapBlock dr db => do
      if hmethod : (mname == "map" || mname == "collect") = true then do
      let r ← checkFlow n ordinary κ Γ I facts recv dr cache
      match hty : r.ty with
      | .arrayOf σ => do
        if hf : nameFreeN r.ctx mname = true then do
        if hm : closureMainB r.ctx r.spine = true then do
        if hσ : FirstOrder σ = true then do
        if hin : activationEnvB ([(name, σ)] ++ blockLocals locals ++ r.out) = true then do
        let b ← ordinary ([(name, σ)] ++ blockLocals locals ++ r.out) body db
          (closureBodyCtx r.ctx) r.spine r.cache
        let ⟨hbctx⟩ ← ctxEq? b.ctx (closureBodyCtx r.ctx)
        if hbspine : b.spine = r.spine then do
        if hρ : FirstOrder b.ty = true then do
        if hout : activationReturnB b.out = true then do
        match hn : r.facts.captureNames? (withoutNames ([name] ++ locals) b.out) with
        | none => none
        | some names =>
          if hfix : closureReturnEnv ([name] ++ locals) names r.out b.out = r.out then
            some ⟨.arrayOf b.ty, false, r.ctx, r.out, r.spine, .unknown,
              .map (by simpa only [hty] using r.judged) hmethod hf hm hσ hρ hn hin hout hfix
                (by simpa only [hbctx, hbspine] using b.judged), b.cache⟩
          else none
        else none
        else none
        else none
        else none
        else none
        else none
        else none
      | _ => none
      else none
    | .send none name [] (some (.block formals locals body)), .callBlock claimed db ret => do
      if name != claimed then none else do
      let c ← findCallback κ I name cache.callbacks
      if hp : c.body.params = [] then do
      if hr : c.body.ret = ret then do
      let ⟨ps, hparams, htypes⟩ ← requiredFlowParams? formals c.body.blockArgs
      if hs : (paramEqAll (ps.map (fun p => Param.req p.1)) (ps.map (fun p => Param.req p.1)) && exprEq body body) = true then do
      if hm : closureMainB κ I = true then do
      if hin : activationEnvB (ps ++ blockLocals locals ++ Γ) = true then do
      let b ← ordinary (ps ++ blockLocals locals ++ Γ) body db (closureBodyCtx κ) I cache
      let ⟨hbctx⟩ ← ctxEq? b.ctx (closureBodyCtx κ)
      if hbi : b.spine = I then do
      if hbr : b.ty = c.body.blockRet then do
      if hout : activationReturnB b.out = true then do
      match hn : facts.captureNames? (withoutNames (ps.map (·.1) ++ locals) b.out) with
      | none => none
      | some names =>
        if hfix : closureReturnEnv (ps.map (·.1) ++ locals) names Γ b.out = Γ then
          some ⟨ret, false, κ, Γ, I, .unknown, by
            have hj := DFlow.callBlock (facts := facts)
              (by simpa only [hp, htypes] using c.body.judged)
              (by simpa only [hp, List.map_nil] using c.body.paramShape) c.installed c.body.returnFO
              c.body.blockReturnFO hm hin hout hfix hn hs
              (by simpa only [hbctx, hbi, hbr] using b.judged)
            simpa only [c.nameOk, hparams, hr] using hj, cache⟩
        else none
      else none
      else none
      else none
      else none
      else none
      else none
      else none
      else none
    | e, d => do
      let c ← ordinary Γ e d κ I cache
      some ⟨c.ty, false, c.ctx, c.out, c.spine, facts.afterEffect, .embed facts c.judged, c.cache⟩

def checkFlowSeq (fuel : Nat) (ordinary : OrdinaryCheck) (κ : Ctx) (Γ : Env) (I : Ty)
    (facts : LocalFacts) (es : List Expr) (ds : List Deriv) (cache : CheckedCache) :
    Option (CertifiedFlowSeq κ Γ I facts es) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match es, ds with
    | [e], [d] => do
      let c ← checkFlow n ordinary κ Γ I facts e d cache
      some ⟨c.ty, c.current, c.ctx, c.out, c.spine, c.facts, .last c.judged, c.cache⟩
    | e :: e' :: es, d :: d' :: ds => do
      let c ← checkFlow n ordinary κ Γ I facts e d cache
      let t ← checkFlowSeq n ordinary c.ctx c.out c.spine c.facts (e' :: es) (d' :: ds) c.cache
      some ⟨t.ty, t.current, t.ctx, t.out, t.spine, t.facts, .cons c.judged t.judged, t.cache⟩
    | _, _ => none

def checkFlowAll (fuel : Nat) (ordinary : OrdinaryCheck) (κ : Ctx) (Γ : Env) (I : Ty)
    (facts : LocalFacts) (es : List Expr) (ds : List Deriv) (cache : CheckedCache) :
    Option (CertifiedFlowAll κ Γ I facts es) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match es, ds with
    | [], [] => some ⟨[], κ, Γ, I, facts, .nil, cache⟩
    | e :: es, d :: ds => do
      if hp : plainArgB e = true then do
      let c ← checkFlow n ordinary κ Γ I facts e d cache
      let t ← checkFlowAll n ordinary c.ctx c.out c.spine c.facts es ds c.cache
      some ⟨c.ty :: t.tys, t.ctx, t.out, t.spine, t.facts, .cons c.judged t.judged hp, t.cache⟩
      else none
    | _, _ => none
end
end Ratchet
