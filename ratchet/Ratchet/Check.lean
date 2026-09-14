import Ratchet.DJudge

set_option autoImplicit false
namespace Ratchet

/-! ## §3 The checker, which *builds* the derivation

`check` does not return a `Ty` and leave soundness to a separate induction — it returns the
`DJudge` term. So layer 3 is not a theorem about layer 2, it is layer 2's **type**, and the
oracle that judges a rung is the Lean typechecker: if `check` compiles, every answer it can
ever give carries a derivation.

That is the same move as `Denote/Clink/`'s `Clink.sem` one level down, and it was chosen over
`check : … → Option (Ty × Env)` plus `check_sound` for a reason worth recording: the latter is
one `induction fuel` with a `split` over a 23-arm match, and every arm of it is a place where
the proof can be *weaker* than the function (an arm whose `none` case is discharged by
`simp` proves nothing about the arm's real behaviour). Here there is no gap to be weaker
across.

**Everything is computed from the program and *compared* against the certificate.** The
program is the authority: `check` matches `e`, derives the type itself, and then asks whether
the certificate agrees. A certificate that names a different literal, a different method, or a
different join is rejected — not because soundness needs it (it does not; the derivation is
about `e` either way) but because a checker that ignores its certificate is not checking one,
and the whole pipeline downstream of `scripts/emit_deriv.py` would be unfalsifiable.
`Ratchet/DerivControls.lean` pins each of those rejections.

### Why fuel

`Deriv` is a nested inductive and `check` is mutual with three list companions; fuel makes the
recursion structural and obviously terminating. Exhaustion answers `none`, so it can only cost
completeness. -/

/-- A body checked at its parameter/return annotations in this context. Calls reuse it. -/
structure CheckedBody (κ : Ctx) (I : Ty) (decl : Defn) where
  params : List SigParam
  ret : Ty
  out : Env
  paramShape : decl.params = params.map (fun p => Param.req p.1)
  paramsFO : ∀ p ∈ params, FirstOrder p.2 = true ∧ isAliasTy p.2 = false
  returnFO : FirstOrder ret = true
  judged : DJudge params decl.body ret out κ I κ I

/-- Checker data, not a new judgment premise. Exact context checks prevent stale proofs
from being reused after a definition, spine change, or incompatible branch. -/
structure CachedBody where
  ctx : Ctx
  spine : Ty
  decl : Defn
  body : CheckedBody ctx spine decl
  /-- Replay hint only. Refresh reconstructs the signature from the checked artifact. -/
  deriv : Deriv

abbrev BodyCache := List CachedBody

structure CallableBody (κ : Ctx) (I : Ty) (name : String) where
  decl : Defn
  nameOk : decl.name = name
  body : CheckedBody (κ.withFrame (some ⟨"Object", "Object", decl.name⟩)) I decl
  installed : decl ∈ κ.defs

def findBody (κ : Ctx) (I : Ty) (name : String) : BodyCache → Option (CallableBody κ I name)
  | [] => none
  | c :: cs =>
    let found : Option (CallableBody κ I name) := do
      if hn : c.decl.name = name then do
        let ⟨hc⟩ ← ctxEq? c.ctx (κ.withFrame (some ⟨"Object", "Object", c.decl.name⟩))
        if hi : c.spine = I then do
          let ⟨hd⟩ ← defnMem? c.decl κ.defs
          some ⟨c.decl, hn, by simpa only [hc, hi] using c.body, hd⟩
        else none
      else none
    found.orElse (fun _ => findBody κ I name cs)

/-- A checked answer: the type and every outgoing state index, with their derivation.
No outgoing declaration table is reconstructed separately from the expression proof. -/
structure Certified (Γ : Env) (e : Expr) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  ty : Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudge Γ e ty out κ I ctx spine
  cache : BodyCache := []

structure CertifiedAll (Γ : Env) (es : List Expr) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  tys : List Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudgeAll Γ es tys out κ I ctx spine
  cache : BodyCache := []

structure CertifiedSeq (Γ : Env) (es : List Expr) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  ty : Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudgeSeq Γ es ty out κ I ctx spine
  cache : BodyCache := []

structure CertifiedPairs (Γ : Env) (ps : List (Expr × Expr)) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  keys : List Ty
  vals : List Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudgePairs Γ ps keys vals out κ I ctx spine
  cache : BodyCache := []

structure CertifiedRec (κ : Ctx) (I : Ty) (s : RecScope) (Γ : Env) (e : Expr) where
  ty : Ty
  out : Env
  judged : DJudgeRec κ I s Γ e ty out

structure CertifiedRecAll (κ : Ctx) (I : Ty) (s : RecScope) (Γ : Env) (es : List Expr) where
  tys : List Ty
  out : Env
  judged : DJudgeRecAll κ I s Γ es tys out

mutual
/-- The program selects the rule; the certificate supplies sub-derivations and checked
claims. Every recursive result carries its actual outgoing context, locals, and spine. -/
def check (fuel : Nat) (Γ : Env) (e : Expr) (d : Deriv) (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : BodyCache := []) :
    Option (Certified Γ e κ I) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match e, d with
    | .int k, .intLit k' => if k == k' then some ⟨.int, Γ, κ, I, .intLit, cache⟩ else none
    | .flt b, .fltLit b' => if b == b' then some ⟨.float, Γ, κ, I, .fltLit, cache⟩ else none
    | .str s, .strLit s' => if s == s' then some ⟨.cls "String", Γ, κ, I, .strLit, cache⟩ else none
    | .sym s, .symLit s' => if s == s' then some ⟨.sym, Γ, κ, I, .symLit, cache⟩ else none
    | .tru, .truLit => some ⟨.bool, Γ, κ, I, .truLit, cache⟩
    | .fls, .flsLit => some ⟨.bool, Γ, κ, I, .flsLit, cache⟩
    | .nil, .nilLit => some ⟨.nilT, Γ, κ, I, .nilLit, cache⟩
    | .vcall "x", .bareName "x" =>
      if hx : nameFreeN κ "x" = true then
        if hm : nameFreeN κ "method_missing" = true then
          if hs : κ.selfTy = none then some ⟨.any, Γ, κ, I, .bareName hx hm hs, cache⟩ else none
        else none
      else none
    | .var .lvar x, .var .lvar x' =>
      if x == x' then
        match hg : envGet? Γ x with
        | some τ => if ha : isAliasTy τ = false then some ⟨τ, Γ, κ, I, .var hg ha, cache⟩ else none
        | none => none
      else none
    | .vasgn .lvar x ev, .vasgn .lvar x' dv =>
      if x == x' then
        match check n Γ ev dv κ I cache with
        | some ⟨τ, Γ₁, κ₁, I₁, hv, cv⟩ =>
          if hcap : capStale x τ τ = false then
            if ha : isAliasTy τ = false then
              if hk : capStaleCtx x τ κ₁ = false then
                some ⟨τ, envAfter Γ₁ x τ, κ₁, killClosOverSpine I₁ x τ, .vasgn hv hcap ha hk, cv⟩
              else none
            else none
          else none
        | none => none
      else none
    | .seq es, .seq ds =>
      match checkSeq n Γ es ds κ I cache with
      | some ⟨τ, Γ', κ', I', hs, cs⟩ => some ⟨τ, Γ', κ', I', .seq hs, cs⟩
      | none => none
    | .send (some recv) m args none, .prim dr dm dargs σc τc =>
      if dm == m then
        match check n Γ recv dr κ I cache with
        | some ⟨σ, Γ₁, κ₁, I₁, hr, cr⟩ =>
          if σ == σc then
            match checkAll n Γ₁ args dargs κ₁ I₁ cr with
            | some ⟨argTys, Γ₂, κ₂, I₂, ha, ca⟩ =>
              match hp : dprim? σ m argTys with
              | some τ =>
                if τ == τc then
                  if hf : nameFreeN κ₂ m = true then
                    if hs : σ = .cls "String" →
                        isANoOk κ₂.wholeCls (["String", "Comparable"] ++ rootAncestors) = true then
                      some ⟨τ, Γ₂, κ₂, I₂, .prim hr ha (dprim?_sound hp) hf hs, ca⟩
                    else none
                  else none
                else none
              | none => none
            | none => none
          else none
        | none => none
      else none
    | .if' c t (some el), .ifD dc dt (some de) j =>
      match check n Γ c dc κ I cache with
      | some ⟨_, Γc, κc, Ic, hc, cc⟩ =>
        match check n Γc t dt κc Ic cc, check n Γc el de κc Ic cc with
        | some ⟨τ₁, Γ₁, κ₁, I₁, ht, ct⟩, some ⟨τ₂, Γ₂, κ₂, I₂, he, _⟩ =>
          if joinT τ₁ τ₂ == j then
            match ctxEq? κ₁ κ₂ with
            | some ⟨hctx⟩ =>
              if hi : I₁ = I₂ then
                some ⟨joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, κ₁, I₁,
                  .if' hc ht (by cases hctx; cases hi; exact he), ct⟩
              else none
            | none => none
          else none
        | _, _ => none
      | none => none
    | .if' c t none, .ifD dc dt none j =>
      match check n Γ c dc κ I cache with
      | some ⟨_, Γc, κc, Ic, hc, cc⟩ =>
        match check n Γc t dt κc Ic cc with
        | some ⟨τ, Γt, κt, It, ht, _⟩ =>
          if joinT τ .nilT == j then
            match ctxEq? κt κc with
            | some ⟨hctx⟩ =>
              if hi : It = Ic then
                some ⟨joinT τ .nilT, joinEnv Γt Γc, κc, Ic,
                  .ifNoElse hc (by cases hctx; cases hi; exact ht), cc⟩
              else none
            | none => none
          else none
        | none => none
      | none => none
    | .array es, .arrayLit ds elem =>
      match checkAll n Γ es ds κ I cache with
      | some ⟨tys, Γ', κ', I', hs, cs⟩ =>
        if elemTy tys == elem then
          if hf : FirstOrder (elemTy tys) = true then
            some ⟨.arrayOf (elemTy tys), Γ', κ', I', .arrayLit hs hf, cs⟩
          else none
        else none
      | none => none
    | .hash ps, .hashLit dks dvs key val =>
      match checkPairs n Γ ps dks dvs κ I cache with
      | some ⟨ks, vs, Γ', κ', I', hs, cs⟩ =>
        if elemTy ks == key && elemTy vs == val then
          if hk : FirstOrder (elemTy ks) = true then
            if hv : FirstOrder (elemTy vs) = true then
              some ⟨.hashOf (elemTy ks) (elemTy vs), Γ', κ', I', .hashLit hs hk hv, cs⟩
            else none
          else none
        else none
      | none => none
    | .def' name formals body, .defDecl name' ps ret db => do
      if name != name' then none else do
      if hm : κ.scope.runtimeMain = true then do
      if hc : κ.classes.isEmpty = true then do
      if hs : κ.selfTy = none then do
      if hb : κ.blockTy = none then do
      if hco : κ.consts = [] then do
      if ha : κ.asms = [] then do
      if hi : FirstOrder I = true then do
      if hg : Γ.all (fun p => FirstOrder (stripAlias p.2)) = true then do
      if hf : κ.defs.all (fun old => old.name != name) = true then do
      if hmiss : "method_missing" ≠ name then do
      if hquiet : "method_added" ≠ name then do
        let decl : Defn := ⟨name, formals, body⟩
        let fresh ← refreshBodies n (topDeclCtx κ decl) I cache
        let c ← checkMethodBody n (topBodyCtx κ decl) I decl (.defDecl name' ps ret db) fresh
        some ⟨.sym, Γ, topDeclCtx κ decl, I,
          .defDecl c.paramShape c.paramsFO c.returnFO c.judged hm
            (List.isEmpty_iff.mp hc) hs hb hco ha hi (List.all_eq_true.mp hg)
            (by simpa only [List.all_eq_true, bne_iff_ne] using hf) hmiss hquiet,
          ⟨topBodyCtx κ decl, I, decl, c, db⟩ :: fresh⟩
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
    | .send none name args none, .callSig name' ds ret => do
      if name != name' then none else do
      let a ← checkAll n Γ args ds κ I cache
      let c ← findBody a.ctx a.spine name a.cache
      if ht : a.tys = c.body.params.map (·.2) then do
      if hr : c.body.ret = ret then do
      if hstart : κ.scope.runtimeMain = true then do
      if hm : a.ctx.scope.runtimeMain = true then do
      if hs : a.ctx.selfTy = none then do
      if hb : a.ctx.blockTy = none then do
      if hco : a.ctx.consts = [] then do
      if ha : a.ctx.asms = [] then do
      if hi : FirstOrder a.spine = true then do
      if hg : a.out.all (fun p => FirstOrder (stripAlias p.2)) = true then
        some ⟨c.body.ret, a.out, a.ctx, a.spine, by
          simpa only [c.nameOk] using
            (DJudge.callSig c.body.paramShape c.body.paramsFO c.body.returnFO c.body.judged
              (by simpa only [ht] using a.judged) c.installed hstart hm hs hb hco ha hi
              (List.all_eq_true.mp hg)), a.cache⟩
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
    | _, _ => none

def checkAll (fuel : Nat) (Γ : Env) (es : List Expr) (ds : List Deriv)
    (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : BodyCache := []) : Option (CertifiedAll Γ es κ I) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match es, ds with
    | [], [] => some ⟨[], Γ, κ, I, .nil, cache⟩
    | e :: es', d :: ds' =>
      match check n Γ e d κ I cache with
      | some ⟨τ, Γ₁, κ₁, I₁, he, ce⟩ =>
        match checkAll n Γ₁ es' ds' κ₁ I₁ ce with
        | some ⟨τs, Γ₂, κ₂, I₂, hr, cr⟩ => some ⟨τ :: τs, Γ₂, κ₂, I₂, .cons he hr he.plainArg, cr⟩
        | none => none
      | none => none
    | _, _ => none

def checkPairs (fuel : Nat) (Γ : Env) (ps : List (Expr × Expr)) (dks dvs : List Deriv)
    (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : BodyCache := []) : Option (CertifiedPairs Γ ps κ I) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match ps, dks, dvs with
    | [], [], [] => some ⟨[], [], Γ, κ, I, .nil, cache⟩
    | (k, v) :: ps', dk :: dks', dv :: dvs' =>
      match check n Γ k dk κ I cache with
      | some ⟨σ, Γk, κk, Ik, hk, ck⟩ =>
        match check n Γk v dv κk Ik ck with
        | some ⟨τ, Γv, κv, Iv, hv, cv⟩ =>
          match checkPairs n Γv ps' dks' dvs' κv Iv cv with
          | some ⟨ks, vs, Γ', κ', I', hs, cs⟩ => some ⟨σ :: ks, τ :: vs, Γ', κ', I', .cons hk hv hs, cs⟩
          | none => none
        | none => none
      | none => none
    | _, _, _ => none

def checkSeq (fuel : Nat) (Γ : Env) (es : List Expr) (ds : List Deriv)
    (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : BodyCache := []) : Option (CertifiedSeq Γ es κ I) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match es, ds with
    | [e], [d] =>
      match check n Γ e d κ I cache with
      | some ⟨τ, Γ', κ', I', he, ce⟩ => some ⟨τ, Γ', κ', I', .last he, ce⟩
      | none => none
    | e :: e' :: es', d :: d' :: ds' =>
      match check n Γ e d κ I cache with
      | some ⟨_, Γ₁, κ₁, I₁, he, ce⟩ =>
        match checkSeq n Γ₁ (e' :: es') (d' :: ds') κ₁ I₁ ce with
        | some ⟨τ, Γ₂, κ₂, I₂, hr, cr⟩ => some ⟨τ, Γ₂, κ₂, I₂, .cons he hr, cr⟩
        | none => none
      | none => none
    | _, _ => none

/-- Check the declaration's body in its annotation environment. Caller locals and
argument values are deliberately not inputs. Return compatibility is exact for now;
subtyping needs a proved denotation-inclusion rule, not the legacy unchecked `subTy`. -/
def checkMethodBody (fuel : Nat) (κ : Ctx) (I : Ty) (decl : Defn) (d : Deriv)
    (cache : BodyCache := []) : Option (CheckedBody κ I decl) :=
  match fuel with
  | 0 => none
  | n + 1 => match d with
  | .defDecl name ps ret db => do
    if name != decl.name then none else do
    if hp : paramEqAll decl.params (ps.map (fun p => Param.req p.1)) = true then do
      if ht : ps.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then do
        if hr : FirstOrder ret = true then do
          let c ← (check n ps decl.body db κ I cache).orElse fun _ => do
            let r ← checkRec n κ I ⟨decl, ps, ret⟩ ps decl.body db cache
            if hret : r.ty = ret then
              if hplain : plainArgB decl.body = true then
                some ⟨ret, r.out, κ, I,
                  .recursive (s := ⟨decl, ps, ret⟩) hplain
                    (by simpa only [hret] using r.judged), cache⟩
              else none
            else none
          if hret : c.ty = ret then do
            let ⟨hctx⟩ ← ctxEq? c.ctx κ
            if hspine : c.spine = I then
              some ⟨ps, ret, c.out, paramEqAll_sound hp,
                by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using ht,
                hr, by simpa only [hret, hctx, hspine] using c.judged⟩
            else none
          else none
        else none
      else none
    else none
  | _ => none

/-- Scoped recursion is a fallback for nodes containing a self-call. Closed subtrees keep
their ordinary derivations; the scope is never inserted into the checked-body cache. -/
def checkRec (fuel : Nat) (κ : Ctx) (I : Ty) (s : RecScope) (Γ : Env)
    (e : Expr) (d : Deriv) (cache : BodyCache) : Option (CertifiedRec κ I s Γ e) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    let closed : Option (CertifiedRec κ I s Γ e) := do
      let c ← check n Γ e d κ I cache
      let ⟨hc⟩ ← ctxEq? c.ctx κ
      if hi : c.spine = I then
        some ⟨c.ty, c.out, .embed (by simpa only [hc, hi] using c.judged)⟩
      else none
    closed.orElse fun _ =>
      match e, d with
      | .send (some recv) name args none, .prim dr name' ds σc τc => do
        if name != name' then none else do
        let r ← checkRec n κ I s Γ recv dr cache
        if r.ty != σc then none else do
        let a ← checkRecAll n κ I s r.out args ds cache
        match hp : dprim? r.ty name a.tys with
        | none => none
        | some τ =>
          if τ != τc then none else
          if hf : nameFreeN κ name = true then
            if hs : r.ty = .cls "String" →
                isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true then
              some ⟨τ, a.out, .prim r.judged a.judged (dprim?_sound hp) hf hs⟩
            else none
          else none
      | .if' c t (some el), .ifD dc dt (some de) j => do
        let c ← checkRec n κ I s Γ c dc cache
        let t ← checkRec n κ I s c.out t dt cache
        let el ← checkRec n κ I s c.out el de cache
        if joinT t.ty el.ty == j then
          some ⟨joinT t.ty el.ty, joinEnv t.out el.out, .if' c.judged t.judged el.judged⟩
        else none
      | .send none name args none, .callSig name' ds ret => do
        if name != name' then none else do
        if hn : s.decl.name = name then do
        if ret != s.ret then none else do
        let a ← checkRecAll n κ I s Γ args ds cache
        if ht : a.tys = s.params.map (·.2) then do
        if hp : paramEqAll s.decl.params (s.params.map (fun p => Param.req p.1)) = true then do
        if hps : s.params.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then do
        if hr : FirstOrder s.ret = true then do
        let ⟨hd⟩ ← defnMem? s.decl κ.defs
        let ⟨hframe⟩ ← ctxEq? (κ.withFrame (some ⟨"Object", "Object", s.decl.name⟩)) κ
        if hm : κ.scope.runtimeMain = true then do
        if hs : κ.selfTy = none then do
        if hb : κ.blockTy = none then do
        if hc : κ.consts = [] then do
        if has : κ.asms = [] then do
        if hi : FirstOrder I = true then do
        if hg : a.out.all (fun p => FirstOrder (stripAlias p.2)) = true then
          some ⟨s.ret, a.out, by
            simpa only [hn] using
              (DJudgeRec.selfCall (by simpa only [ht] using a.judged) (paramEqAll_sound hp)
                (by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using hps)
                hr hd hframe hm hs hb hc has hi (List.all_eq_true.mp hg))⟩
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
        else none
      | _, _ => none

def checkRecAll (fuel : Nat) (κ : Ctx) (I : Ty) (s : RecScope) (Γ : Env)
    (es : List Expr) (ds : List Deriv) (cache : BodyCache) : Option (CertifiedRecAll κ I s Γ es) :=
  match fuel with
  | 0 => none
  | n + 1 => match es, ds with
    | [], [] => some ⟨[], Γ, .nil⟩
    | e :: es, d :: ds => do
      let c ← checkRec n κ I s Γ e d cache
      let cs ← checkRecAll n κ I s c.out es ds cache
      if hp : plainArgB e = true then
        some ⟨c.ty :: cs.tys, cs.out, .cons c.judged cs.judged hp⟩
      else none
    | _, _ => none

/-- Recheck existing bodies when a definition changes their context, oldest first so calls
can use already-refreshed predecessors. This runs at definitions, never at calls. The old
artifact supplies the annotations; a replay hint cannot silently change the signature. -/
def refreshBodies (fuel : Nat) (κ : Ctx) (I : Ty) (cache : BodyCache) : Option BodyCache :=
  match fuel with
  | 0 => none
  | n + 1 => match cache with
    | [] => some []
    | c :: cs => do
      let fresh ← refreshBodies n κ I cs
      let bodyCtx := κ.withFrame (some ⟨"Object", "Object", c.decl.name⟩)
      let body ← checkMethodBody n bodyCtx I c.decl
        (.defDecl c.decl.name c.body.params c.body.ret c.deriv) fresh
      some (⟨bodyCtx, I, c.decl, body, c.deriv⟩ :: fresh)
end

/-! ## §4 The entry point

`validate` in the sense the ladder means it: a program, a certificate, a `Bool`. The `Bool`
is `isSome` of a value whose type contains the derivation, so `true` *is* "there is a
`DJudge` derivation of this program", with no theorem in between.

Fuel: 200 is far beyond anything in the corpus (the deepest rung nests ~12 levels) and is not
a soundness parameter -- running out answers `false`. -/

def fuelD : Nat := 200

/-- The certified judgment, as a proposition about a program: it types at *some* type in the
empty environment. -/
def DTyped (p : Expr) : Prop := ∃ τ Γ' κ' I', DJudge [] p τ Γ' ctx0 .ivar0 κ' I'

/-- **The ladder's verdict.** `true` iff the certificate checks. -/
def validateD (p : Expr) (d : Deriv) : Bool := (check fuelD [] p d).isSome

/-- …and the verdict means what it says, by construction rather than by induction: this is
one `match`, because the `Certified` the checker returned carries the derivation. -/
theorem validateD_typed {p : Expr} {d : Deriv} (h : validateD p d = true) : DTyped p := by
  unfold validateD at h
  match hc : check fuelD [] p d with
  | some c => exact ⟨c.ty, c.out, c.ctx, c.spine, c.judged⟩
  | none => rw [hc] at h; exact absurd h (by simp)

/-! ## §5 Semantic status

`validateD p d = true` means the checker returned a `DJudge` derivation of `p`.
All nineteen expression rules and twelve companion rules have answer-typed semantic proofs
registered in `Denote/Typed/Clink.lean`. The semantic target includes safety under a typed
continuation, so escapes and halts are covered as well as returned values.

`Denote/Typed/Bridge.lean` proves `validateD_safe_boot` for every accepted certificate.
`CorpusSafety.lean` additionally carries worked derivations exercising every registered rule;
`RuleAudit.lean` checks their proof terms, and `SemLadder.lean` cross-checks their programs.

`Ratchet/Judge.lean` is the retained type/context substrate. The older judgment and checker
were deleted in clink 68; the current proof boundary is the answer-typed registry. -/

end Ratchet
