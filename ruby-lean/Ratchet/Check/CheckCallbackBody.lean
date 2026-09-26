import Ratchet.Check.MethodCertificate

/-! Source/certificate checking for DMethod, independent of the eventual callback.
Each successful branch returns its derivation. This is staged: validateD does not yet
admit a method definition or call through these certificates. -/
set_option autoImplicit false
namespace Ratchet

mutual
def checkCallbackExpr (fuel : Nat) (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γ : Env) (e : Expr) (d : Deriv) : Option (CertifiedMethod κ I fr ps ret Γ e) :=
  match fuel with
  | 0 => none
  | n + 1 => match e, d with
    | .int a, .intLit b => if a == b then some (.ofOrdinary fun _ => .intLit) else none
    | .flt a, .fltLit b => if a == b then some (.ofOrdinary fun _ => .fltLit) else none
    | .str a, .strLit b => if a == b then some (.ofOrdinary fun _ => .strLit) else none
    | .sym a, .symLit b => if a == b then some (.ofOrdinary fun _ => .symLit) else none
    | .tru, .truLit => some (.ofOrdinary fun _ => .truLit)
    | .fls, .flsLit => some (.ofOrdinary fun _ => .flsLit)
    | .nil, .nilLit => some (.ofOrdinary fun _ => .nilLit)
    | .var .lvar x, .var .lvar y => do
      if x != y then none else do
      match hg : envGet? Γ x with
      | none => none
      | some τ => if ha : isAliasTy τ = false then some (.ofOrdinary fun _ => .var hg ha) else none
    | .vasgn .lvar x e, .vasgn .lvar y d => do
      if x != y then none else do
      let c ← checkCallbackExpr n κ I fr ps ret Γ e d
      if hc : capStale x c.ty c.ty = false then do
      if ha : isAliasTy c.ty = false then do
      if hk : capStaleCtx x c.ty (callbackMethodCtx κ fr default) = false then do
      if hi : killClosOverSpine I x c.ty = I then
        let guard := fun code => (callback_capStale κ fr x c.ty code).trans hk
        let ordinary := c.ordinary.map fun ⟨h⟩ => PLift.up fun code => by
          simpa only [hi] using DJudge.vasgn (h code) hc ha (guard code)
        some ⟨c.ty, envAfter c.out x c.ty, .vasgn c.judged hc ha guard hi, ordinary⟩
      else none
      else none
      else none
      else none
    | .seq es, .seq ds => do
      let c ← checkCallbackSeq n κ I fr ps ret Γ es ds
      some ⟨c.ty, c.out, .sequence c.judged, c.ordinary.map fun ⟨h⟩ => PLift.up fun code => DJudge.seq (h code)⟩
    | .send (some recv) name args none, .prim dr claimed ds recvTy retTy => do
      if name != claimed then none else do
      let r ← checkCallbackExpr n κ I fr ps ret Γ recv dr
      if r.ty != recvTy then none else do
      let a ← checkCallbackAll n κ I fr ps ret r.out args ds
      match hp : dprim? r.ty name a.tys with
      | none => none
      | some τ => do
        if τ != retTy then none else do
        if hf : nameFreeN κ name = true then do
        if hs : r.ty = .cls "String" → isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true then
          let ordinary := do
            let ⟨hr⟩ ← r.ordinary
            let ⟨ha⟩ ← a.ordinary
            some (PLift.up fun code => DJudge.prim (hr code) (ha code) (dprim?_sound hp) hf hs)
          some ⟨τ, a.out, .prim r.judged a.judged (dprim?_sound hp) hf hs, ordinary⟩
        else none
        else none
    | .yield' [arg], .yieldArgs [da] => do
      match hps : ps with
      | [σ] => do
        let a ← checkCallbackExpr n κ I fr ps ret Γ arg da
        if ht : a.ty = σ then do
        if he : activationReturnB a.out = true then do
        if hp : plainArgB arg = true then
          some ⟨ret, a.out, by simpa only [hps] using
            (DMethod.yieldOne (by simpa only [hps, ht] using a.judged) he hp), none⟩
        else none
        else none
        else none
      | _ => none
    | .array es, .arrayLit ds elem => do
      let a ← checkCallbackAll n κ I fr ps ret Γ es ds
      if elemTy a.tys != elem then none else do
      if hf : FirstOrder (elemTy a.tys) = true then do
        let ⟨h⟩ ← a.ordinary
        some (.ofOrdinary fun code => .arrayLit (h code) hf)
      else none
    | _, _ => none

def checkCallbackAll (fuel : Nat) (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γ : Env) (es : List Expr) (ds : List Deriv) : Option (CertifiedMethodAll κ I fr ps ret Γ es) :=
  match fuel with
  | 0 => none
  | n + 1 => match es, ds with
    | [], [] => some ⟨[], Γ, .nil, some ⟨fun _ => .nil⟩⟩
    | e :: es, d :: ds => do
      if hp : plainArgB e = true then do
        let h ← checkCallbackExpr n κ I fr ps ret Γ e d
        let t ← checkCallbackAll n κ I fr ps ret h.out es ds
        let ordinary := do
          let ⟨he⟩ ← h.ordinary
          let ⟨ht⟩ ← t.ordinary
          some (PLift.up fun code => DJudgeAll.cons (he code) (ht code) hp)
        some ⟨h.ty :: t.tys, t.out, .cons h.judged t.judged hp, ordinary⟩
      else none
    | _, _ => none

def checkCallbackSeq (fuel : Nat) (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γ : Env) (es : List Expr) (ds : List Deriv) : Option (CertifiedMethodSeq κ I fr ps ret Γ es) :=
  match fuel with
  | 0 => none
  | n + 1 => match es, ds with
    | [e], [d] => do
      let c ← checkCallbackExpr n κ I fr ps ret Γ e d
      some ⟨c.ty, c.out, .last c.judged, c.ordinary.map fun ⟨h⟩ => PLift.up fun code => DJudgeSeq.last (h code)⟩
    | e :: e' :: es, d :: d' :: ds => do
      let h ← checkCallbackExpr n κ I fr ps ret Γ e d
      let t ← checkCallbackSeq n κ I fr ps ret h.out (e' :: es) (d' :: ds)
      let ordinary := do
        let ⟨he⟩ ← h.ordinary
        let ⟨ht⟩ ← t.ordinary
        some (PLift.up fun code => DJudgeSeq.cons (he code) (ht code))
      some ⟨t.ty, t.out, .cons h.judged t.judged, ordinary⟩
    | _, _ => none
end

/-- Check a whole declaration against its proposed signature, including uncalled bodies.
No call argument or captured environment participates in this decision. Sorbet 0.6.13405
accepts `yield(value)` at Integer and rejects a nilable Integer domain (7002, clink 237). -/
def checkCallbackBody (fuel : Nat) (κ : Ctx) (I : Ty) (decl : Defn) (hint : Deriv) :
    Option (CheckedCallbackBody κ I decl) := do
  match hint with
  | .defBlock name params bs br ret body => do
    if name != decl.name then none else do
    if hp : paramEqAll decl.params (params.map (fun p => Param.req p.1)) = true then do
    if ht : params.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then do
    if hb : bs.all (fun τ => FirstOrder τ && !isAliasTy τ) = true then do
    if hbr : FirstOrder br = true then do
    if hr : FirstOrder ret = true then do
      let c ← checkCallbackExpr fuel κ I ⟨"Object", "Object", decl.name, false⟩ bs br params decl.body body
      if hret : c.ty = ret then
        some ⟨params, bs, br, ret, c.out, paramEqAll_sound hp, ht, hb, hbr, hr, hret ▸ c.judged⟩
      else none
    else none
    else none
    else none
    else none
    else none
  | _ => none

end Ratchet
