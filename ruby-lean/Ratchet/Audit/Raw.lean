-- Generated from Ratchet/Check/Raw.lean by scripts/generate_audited_checker.py.
-- Edit the raw source and regenerate; Lean checks the indexed proof and trace.
import Ratchet.Audit.Erase
import Ratchet.Audit.CallbackCache
import Ratchet.Audit.FlowCheck
import Ratchet.Check.OptShape

set_option autoImplicit false
namespace Ratchet.Audit
open Ratchet

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
and the whole pipeline downstream of `scripts/emit_deriv.rb` would be unfalsifiable.
`Ratchet/Controls/DerivControls.lean` pins each of those rejections.

### Why fuel

`Deriv` is a nested inductive and `check` is mutual with three list companions; fuel makes the
recursion structural and obviously terminating. Exhaustion answers `none`, so it can only cost
completeness. -/


mutual
/-- The program selects the rule; the certificate supplies sub-derivations and checked
claims. Every recursive result carries its actual outgoing context, locals, and spine. -/
def check (fuel : Nat) (Γ : Env) (e : Expr) (d : Deriv) (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : CheckedCache := {}) :
    Option (Certified Γ e κ I) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match e, d with
    | e, .flow d => do
      let c ← checkFlow n (fun Γ e d κ I cache => check n Γ e d κ I cache) κ Γ I .unknown e d cache
      some ⟨c.ty, c.out, c.ctx, c.spine, .flow c.judged, c.cache⟩
    | .int k, .intLit k' => if k == k' then some ⟨.int, Γ, κ, I, .intLit, cache⟩ else none
    | .flt b, .fltLit b' => if b == b' then some ⟨.float, Γ, κ, I, .fltLit, cache⟩ else none
    | .regexpLit s o, .regexpLit s' o' =>
      if s == s' && o == o' then some ⟨.cls "Regexp", Γ, κ, I, .regexpLit, cache⟩ else none
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
    | .vcall name, .callSig claimed [] ret => do
      if name != claimed then none else do
      match hs : κ.selfTy with
      | some (.inst cn fields) => do
        let f ← findClass cn κ.classes
        let c ← findMember κ f.cls name cache.members
        if hf : fields = c.fields then do
        if hp : c.body.params = [] then do
        let result ← c.body.resultAt ret
        if hn : c.decl.name ≠ "initialize" then do
        if hd : directCallNameB c.decl.name = true then do
        if hg : instanceCallB κ Γ I = true then
          some ⟨ret, Γ, κ, I, by
            simpa only [c.nameOk] using
              (DJudge.vcallMethodSig (Γ := Γ) (I := I)
                (by simpa only [f.nameOk, hf] using hs) f.member c.installed hn hd
                (by simpa only [hp, List.map_nil] using c.body.paramShape)
                result.firstOrder c.fieldsFO (by simpa only [hp] using result.judged) hg), cache⟩
        else none
        else none
        else none
        else none
        else none
      | some (.clsOf _) =>
        checkImplicitSingleton n Γ (.vcall name) name [] [] ret .vcall κ I cache
      | _ => none
    | .self', .selfExpr => do
      match hs : κ.selfTy with
      | some τ => some ⟨τ, Γ, κ, I, .selfRead hs, cache⟩
      | none => none
    | .var .lvar x, .var .lvar x' =>
      if x == x' then
        match hg : envGet? Γ x with
        | some τ => if ha : isAliasTy τ = false then some ⟨τ, Γ, κ, I, .var hg ha, cache⟩ else none
        | none => none
      else none
    | .var .ivar x, .ivarRead y ty =>
      if x == y && κ.ivarReadTy I x == ty then
        some ⟨κ.ivarReadTy I x, Γ, κ, I, .ivarRead, cache⟩ else none
    | .const name, .constCls claimed => do
      if name != claimed then none else do
      let c ← findClass name κ.classes
      some ⟨.clsOf name, Γ, κ, I, by
        simpa only [c.nameOk] using (DJudge.constClass (Γ := Γ) (I := I) c.member), cache⟩
    | .class' name none body, .classDecl claimed none db =>
      if name != claimed then none else
      (do
        let c ← check n [] body db (classHeaderCtx (classBodyCtx κ name) name) .ivar0 cache
        if hg : classRuleB κ c.ctx Γ I c.ty name = true then do
          let fresh ← refreshBodies n (returnScopeCtx κ c.ctx) I c.cache
          some ⟨c.ty, Γ, returnScopeCtx κ c.ctx, I, .classDecl c.judged hg, fresh⟩
        else none) <|>
      (do
        let f ← findClass name κ.classes
        if hmod : f.cls.isModule = false then do
          let c ← check n [] body db (reopenBodyCtx κ f.cls.name) .ivar0 cache
          if hg : reopenRuleB κ c.ctx Γ I c.ty f.cls.name = true then do
            let fresh ← refreshBodies n (returnScopeCtx κ c.ctx) I c.cache
            some ⟨c.ty, Γ, returnScopeCtx κ c.ctx, I, by
              simpa only [f.nameOk] using DJudge.classReopen f.member hmod c.judged hg, fresh⟩
          else none
        else none)
    | .module' name body, .moduleDecl claimed db => do
      if name != claimed then none else do
      let c ← check n [] body db (moduleHeaderCtx (moduleBodyCtx κ name) name) .ivar0 cache
      if hg : moduleRuleB κ c.ctx Γ I c.ty name = true then do
        let fresh ← refreshBodies n (returnScopeCtx κ c.ctx) I c.cache
        some ⟨c.ty, Γ, returnScopeCtx κ c.ctx, I, .moduleDecl c.judged hg, fresh⟩
      else none
    | .class' name (some super) body, .classDecl claimed (some parent) db => do
      if name != claimed then none else do
      let s ← check n Γ super (.constCls parent) κ I cache
      let f ← findClass parent s.ctx.classes
      if ht : s.ty = .clsOf f.cls.name then do
        let c ← check n [] body db
          (subclassHeaderCtx (classBodyCtx s.ctx name) name f.cls.name) .ivar0 s.cache
        if hg : subclassRuleB s.ctx c.ctx s.out s.spine c.ty name f.cls.name = true then do
          let fresh ← refreshBodies n (returnScopeCtx s.ctx c.ctx) s.spine c.cache
          some ⟨c.ty, s.out, returnScopeCtx s.ctx c.ctx, s.spine,
            .subclassDecl (by simpa only [ht] using s.judged) f.member c.judged hg, fresh⟩
        else none
      else none
    | .send (some (.const name)) "new" args none, .newInst claimed ds ty => do
      if name != claimed then none else do
      let start ← findClass name κ.classes
      let a ← checkAll n Γ args ds κ I cache
      let f ← findClass name a.ctx.classes
      if hn : smroGet? a.ctx.classes f.cls.name "new" = none then do
      if hp : f.cls.name ∈ a.ctx.pos.plainAlloc then do
        have hr : DJudge Γ (.const name) (.clsOf f.cls.name) Γ κ I := by
          simpa only [start.nameOk, f.nameOk] using (DJudge.constClass (Γ := Γ) (I := I) start.member)
        if hd : noDeclaredSelectorB a.ctx.classes f.cls.name "initialize" = true then do
          if ht : a.tys = [] then do
          let fields := defaultReceiverFields a.ctx f.cls.name
          if ty != .inst name fields then none else do
          if hf : nilFieldsB fields = true then do
          if hroot : rootInitFreeB a.ctx.defs = true then
            some ⟨.inst name fields, a.out, a.ctx, a.spine, by
              simpa only [f.nameOk] using
                (DJudge.newDefault hr (by simpa only [ht] using a.judged) rfl f.member hn hp hd hroot hf), a.cache⟩
          else none
          else none
          else none
        else do
          let c ← findInitializerAt a.ctx f.cls a.cache.initializers
          if ht : a.tys = c.body.params.map (·.2) then do
          if ty != .inst name c.body.fields then none else do
          if hg : mainCallB a.ctx a.out a.spine = true then do
            if ho : c.owner = f.cls.name then do
              let ⟨hd⟩ ← defnMem? c.decl f.cls.methods
              some ⟨.inst name c.body.fields, a.out, a.ctx, a.spine, by
                simpa only [f.nameOk] using
                  (DJudge.newInst hr (by simpa only [ht] using a.judged) rfl f.member hd
                    c.nameOk hn hp c.body.paramShape c.body.paramsFO c.body.returnFO c.body.fieldsFO
                    (by simpa only [ho, initializerBodyCtx] using c.body.judged) hg), a.cache⟩
            else
              some ⟨.inst name c.body.fields, a.out, a.ctx, a.spine, by
                simpa only [f.nameOk] using
                  (DJudge.newInherited hr (by simpa only [ht] using a.judged) rfl f.member c.route
                    c.nameOk hn hp c.body.paramShape c.body.paramsFO c.body.returnFO c.body.fieldsFO
                    c.body.judged hg), a.cache⟩
          else none
          else none
      else none
      else none
    | .send none "new" args none, .newImplicit name ds ty => do
      let a ← checkAll n Γ args ds κ I cache
      let f ← findClass name a.ctx.classes
      if hs : κ.selfTy = some (.clsOf f.cls.name) then do
      let c ← findInitializer a.ctx f.cls a.cache.initializers
      if ht : a.tys = c.body.params.map (·.2) then do
      if ty != .inst name c.body.fields then none else do
      if hn : smroGet? a.ctx.classes f.cls.name "new" = none then do
      if hp : f.cls.name ∈ a.ctx.pos.plainAlloc then do
      if hg : instanceCallB a.ctx a.out a.spine = true then
        some ⟨.inst name c.body.fields, a.out, a.ctx, a.spine, by
          simpa only [f.nameOk] using
            (DJudge.newImplicit hs (by simpa only [ht] using a.judged) f.member c.installed
              c.nameOk hn hp c.body.paramShape c.body.paramsFO c.body.returnFO c.body.fieldsFO
              c.body.judged hg), a.cache⟩
      else none
      else none
      else none
      else none
      else none
    | .send (some recv) name args none, .callSingleton dr claimed ds ret => do
      if name != claimed then none else do
      let r ← check n Γ recv dr κ I cache
      match hrty : r.ty with
      | .clsOf cn => do
        let a ← checkAll n r.out args ds r.ctx r.spine r.cache
        let f ← findClass cn a.ctx.classes
        let c ← findSingleton a.ctx f.cls name a.cache.singletons
        if ht : a.tys = c.body.params.map (·.2) then do
        let result ← c.body.resultAt ret
        if hn : directCallNameB c.decl.name = true then do
        if hg : instanceCallB a.ctx a.out a.spine = true then
          some ⟨ret, a.out, a.ctx, a.spine, by
            simpa only [c.nameOk] using
              (DJudge.callSingleton (by simpa only [hrty, f.nameOk] using r.judged)
                (by simpa only [ht] using a.judged) f.member c.installed hn
                c.body.paramShape c.body.paramsFO result.firstOrder result.judged hg), a.cache⟩
        else none
        else none
        else none
      | _ => none
    | .defs .self' name params body, .defDecl claimed ps ret db => do
      let some cn := κ.scope.runtimeClass | none
      checkSingletonDefinition n κ Γ I cn ⟨name, params, body⟩ (.defDecl claimed ps ret db) cache
    | .send (some recv) name args none, .callMethodSig dr claimed ds ret => do
      if name != claimed then none else do
      let r ← check n Γ recv dr κ I cache
      match hrty : r.ty with
      | .inst cn fields => do
        let a ← checkAll n r.out args ds r.ctx r.spine r.cache
        let f ← findClass cn a.ctx.classes
        let c ← findMemberAt a.ctx f.cls name a.cache.members
        if hf : fields = c.fields then do
        if ht : a.tys = c.body.params.map (·.2) then do
        let result ← c.body.resultAt ret
        if hs : explicitReceiverB recv = true then do
        if hn : c.decl.name ≠ "initialize" then do
        if hd : directCallNameB c.decl.name = true then do
        if hg : instanceCallB a.ctx a.out a.spine = true then do
          have hr : DJudge Γ recv (.inst f.cls.name c.fields) r.out κ I r.ctx r.spine := by
            simpa only [hrty, hf, f.nameOk] using r.judged
          if ho : c.owner = f.cls.name then do
            let ⟨hm⟩ ← defnMem? c.decl f.cls.methods
            some ⟨ret, a.out, a.ctx, a.spine, by
              simpa only [c.nameOk] using
                (DJudge.callMethodSig hr (by simpa only [ht] using a.judged) hs f.member hm
                  hn hd c.body.paramShape c.body.paramsFO result.firstOrder c.fieldsFO
                  (c.own_judged ho result.judged) hg), a.cache⟩
          else if hnative : nativeInstanceFreeB c.decl.name = true then
            some ⟨ret, a.out, a.ctx, a.spine, by
              simpa only [c.nameOk] using
                (DJudge.callInherited hr (by simpa only [ht] using a.judged) hs f.member c.route
                  hn hd hnative c.body.paramShape c.body.paramsFO result.firstOrder c.fieldsFO result.judged hg), a.cache⟩
          else none
        else none
        else none
        else none
        else none
        else none
        else none
      | _ => none
    | .vasgn .ivar x ev, .ivarAsgn claimed dv => do
      if x != claimed then none else do
      let c ← check n Γ ev dv κ I cache
      let some (.inst cn _) := c.ctx.selfTy | none
      if hs : c.ctx.selfTy = some (.inst cn c.spine) then do
      if hx : ivarGet? c.spine x = some c.ty then do
      if hρ : scalarWriteB c.ty = true then do
      if ht : reframeTypesB c.ctx c.spine = true then do
      if hg : localTypesB c.out = true then
        some ⟨c.ty, c.out, c.ctx, c.spine, .scalarIvarAsgn c.judged hs hx hρ ht hg, c.cache⟩
      else none
      else none
      else none
      else none
      else none
    | .send (some (.var .lvar x)) name args blk, .sendUnion dl dr j =>
      match hx : envGet? Γ x with
      | some (.union σ₁ σ₂) =>
        if ha₁ : isAliasTy σ₁ = false then
          if ha₂ : isAliasTy σ₂ = false then
            match check n (envSet Γ x σ₁) (.send (some (.var .lvar x)) name args blk) dl κ I cache,
                check n (envSet Γ x σ₂) (.send (some (.var .lvar x)) name args blk) dr κ I cache with
            | some ⟨τ₁, Γ₁, κ₁, I₁, hl, cl⟩, some ⟨τ₂, Γ₂, κ₂, I₂, hr, cr⟩ =>
              if joinT τ₁ τ₂ == j && cacheSignaturesB cl cr then
                match ctxEq? κ₁ κ₂ with
                | some ⟨hctx⟩ =>
                  if hi : I₁ = I₂ then
                    some ⟨joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, κ₁, I₁,
                      .sendUnion (used_0 := DJudge.rules hl) (used_1 := DJudge.rules hr) hx ha₁ ha₂ hl (by simpa only [DJudge.rules, hctx, hi] using hr), cl⟩
                  else none
                | none => none
              else none
            | _, _ => none
          else none
        else none
      | _ => none
    | .vasgn .lvar t (.var .lvar x), .vasgnAlias =>
      match hx : envGet? Γ x with
      | some σ =>
        if ha : isAliasTy σ = false then
          if hne : x ≠ t then
            if hc : capStale t σ σ = false then
              if hk : capStaleCtx t σ κ = false then
                some ⟨σ, envSet (killClosOver (killAliasesTo Γ t) t σ) t (.sameAs x σ), κ,
                  killClosOverSpine I t σ, .vasgnAlias hx ha hne hc hk, cache⟩
              else none
            else none
          else none
        else none
      | none => none
    | .if' (.send (some (.const cn)) "===" [.var .lvar t] none) th (some el), .ifCaseEq dt de j =>
      match ht : envGet? Γ t with
      | some (.sameAs x ρ) =>
        match hx : envGet? Γ x with
        | some ρ' =>
          if hρ : ρ' = ρ then
            if hg : ifIsAB κ ρ cn = true then
              if hf : nameFreeN κ "===" = true then
                match check n (envSet (envSet Γ x (isATy κ.classes κ.wholeCls cn ρ)) t
                      (.sameAs x (isATy κ.classes κ.wholeCls cn ρ))) th dt κ I cache,
                    check n (envSet (envSet Γ x (notATy κ.classes κ.wholeCls cn ρ)) t
                      (.sameAs x (notATy κ.classes κ.wholeCls cn ρ))) el de κ I cache with
                | some ⟨τ₁, Γ₁, κ₁, I₁, hth, ct⟩, some ⟨τ₂, Γ₂, κ₂, I₂, he, ce⟩ =>
                  if joinT τ₁ τ₂ == j && cacheSignaturesB ct ce then
                    match ctxEq? κ₁ κ₂ with
                    | some ⟨hctx⟩ =>
                      if hi : I₁ = I₂ then
                        some ⟨joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, κ₁, I₁,
                          .ifCaseEq (used_0 := DJudge.rules hth) (used_1 := DJudge.rules he) ht (hρ ▸ hx) hg hf hth (by simpa only [DJudge.rules, hctx, hi] using he), ct⟩
                      else none
                    | none => none
                  else none
                | _, _ => none
              else none
            else none
          else none
        | none => none
      | some ρ =>
        if hg : ifIsAB κ ρ cn = true then
          if hf : nameFreeN κ "===" = true then
            match check n (envSet Γ t (isATy κ.classes κ.wholeCls cn ρ)) th dt κ I cache,
                check n (envSet Γ t (notATy κ.classes κ.wholeCls cn ρ)) el de κ I cache with
            | some ⟨τ₁, Γ₁, κ₁, I₁, hth, ct⟩, some ⟨τ₂, Γ₂, κ₂, I₂, he, ce⟩ =>
              if joinT τ₁ τ₂ == j && cacheSignaturesB ct ce then
                match ctxEq? κ₁ κ₂ with
                | some ⟨hctx⟩ =>
                  if hi : I₁ = I₂ then
                    some ⟨joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, κ₁, I₁,
                      .ifCaseEqVar (used_0 := DJudge.rules hth) (used_1 := DJudge.rules he) ht hg hf hth (by simpa only [DJudge.rules, hctx, hi] using he), ct⟩
                  else none
                | none => none
              else none
            | _, _ => none
          else none
        else none
      | none => none
    | e, .dead x =>
      match hx : envGet? Γ x with
      | some τ =>
        if hn : stripAlias τ = .never then
          if hp : plainArgB e = true then some ⟨.never, Γ, κ, I, .dead hx hn hp, cache⟩ else none
        else none
      | none => none
    | e, .widen d σ =>
      match check n Γ e d κ I cache with
      | some ⟨τ, Γ', κ', I', h, c⟩ => some ⟨joinT τ σ, Γ', κ', I', .widen σ h, c⟩
      | none => none
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
        | some ⟨τ₁, Γ₁, κ₁, I₁, ht, ct⟩, some ⟨τ₂, Γ₂, κ₂, I₂, he, ce⟩ =>
          if joinT τ₁ τ₂ == j && cacheSignaturesB ct ce then
            match ctxEq? κ₁ κ₂ with
            | some ⟨hctx⟩ =>
              if hi : I₁ = I₂ then
                some ⟨joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, κ₁, I₁,
                  .if' (used_0 := DJudge.rules hc) (used_1 := DJudge.rules ht) (used_2 := DJudge.rules he) hc ht (by simpa only [DJudge.rules, hctx, hi] using he), ct⟩
              else none
            | none => none
          else none
        | _, _ => none
      | none => none
    | .if' (.var .lvar x) t (some el), .ifTruthy y dt de j =>
      if x != y then none else
      match hx : envGet? Γ x with
      | some (.nilable σ) =>
        if hf : falseFreeB σ = true then
          if ha : isAliasTy σ = false then
            match check n (envSet Γ x σ) t dt κ I cache, check n (envSet Γ x .nilT) el de κ I cache with
            | some ⟨τ₁, Γ₁, κ₁, I₁, ht, ct⟩, some ⟨τ₂, Γ₂, κ₂, I₂, he, ce⟩ =>
              if joinT τ₁ τ₂ == j && cacheSignaturesB ct ce then
                match ctxEq? κ₁ κ₂ with
                | some ⟨hctx⟩ =>
                  if hi : I₁ = I₂ then
                    some ⟨joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, κ₁, I₁,
                      .ifTruthy (used_0 := DJudge.rules ht) (used_1 := DJudge.rules he) hx hf ha ht (by simpa only [DJudge.rules, hctx, hi] using he), ct⟩
                  else none
                | none => none
              else none
            | _, _ => none
          else none
        else none
      | _ => none
    | .if' (.send (some (.var .lvar x)) "nil?" [] none) t (some el), .ifNilQuery y dt de j =>
      if x != y then none else
      match hx : envGet? Γ x with
      | some ρ =>
        if hg : ifNilQB κ ρ = true then
          match check n (envSet Γ x (nilYesTy ρ)) t dt κ I cache,
              check n (envSet Γ x (nonNilTy ρ)) el de κ I cache with
          | some ⟨τ₁, Γ₁, κ₁, I₁, ht, ct⟩, some ⟨τ₂, Γ₂, κ₂, I₂, he, ce⟩ =>
            if joinT τ₁ τ₂ == j && cacheSignaturesB ct ce then
              match ctxEq? κ₁ κ₂ with
              | some ⟨hctx⟩ =>
                if hi : I₁ = I₂ then
                  some ⟨joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, κ₁, I₁,
                    .ifNilQuery (used_0 := DJudge.rules ht) (used_1 := DJudge.rules he) hx hg ht (by simpa only [DJudge.rules, hctx, hi] using he), ct⟩
                else none
              | none => none
            else none
          | _, _ => none
        else none
      | none => none
    | .if' (.var .lvar x) t none, .ifTruthyNoElse y dt j =>
      if x != y then none else
      match hx : envGet? Γ x with
      | some (.nilable σ) =>
        if hf : falseFreeB σ = true then
          if ha : isAliasTy σ = false then
            match check n (envSet Γ x σ) t dt κ I cache with
            | some ⟨τ, Γt, κt, It, ht, ct⟩ =>
              if joinT τ .nilT == j && cacheSignaturesB ct cache then
                match ctxEq? κt κ with
                | some ⟨hctx⟩ =>
                  if hi : It = I then
                    some ⟨joinT τ .nilT, joinEnv Γt (envSet Γ x .nilT), κ, I,
                      .ifTruthyNoElse (used_0 := DJudge.rules ht) hx hf ha (by simpa only [DJudge.rules, hctx, hi] using ht), cache⟩
                  else none
                | none => none
              else none
            | none => none
          else none
        else none
      | _ => none
    | .if' (.send (some (.var .lvar x)) "nil?" [] none) t _, .ifNilQueryNil y dt =>
      if x != y then none else
      match hx : envGet? Γ x with
      | some .nilT =>
        if hf : nameFreeN κ "nil?" = true then
          match check n Γ t dt κ I cache with
          | some ⟨τ, Γ', κ', I', h, c⟩ => some ⟨τ, Γ', κ', I', .ifNilQueryNil hx hf h, c⟩
          | none => none
        else none
      | _ => none
    | .if' (.send (some (.var .lvar x)) "is_a?" [.const cn] none) t (some el), .ifIsA y cn' dt de j =>
      if x != y || cn != cn' then none else
      match hx : envGet? Γ x with
      | some ρ =>
        if hg : ifIsAB κ ρ cn = true then
          match check n (envSet Γ x (isATy κ.classes κ.wholeCls cn ρ)) t dt κ I cache,
              check n (envSet Γ x (notATy κ.classes κ.wholeCls cn ρ)) el de κ I cache with
          | some ⟨τ₁, Γ₁, κ₁, I₁, ht, ct⟩, some ⟨τ₂, Γ₂, κ₂, I₂, he, ce⟩ =>
            if joinT τ₁ τ₂ == j && cacheSignaturesB ct ce then
              match ctxEq? κ₁ κ₂ with
              | some ⟨hctx⟩ =>
                if hi : I₁ = I₂ then
                  some ⟨joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, κ₁, I₁,
                    .ifIsA (used_0 := DJudge.rules ht) (used_1 := DJudge.rules he) hx hg ht (by simpa only [DJudge.rules, hctx, hi] using he), ct⟩
                else none
              | none => none
            else none
          | _, _ => none
        else none
      | none => none
    | .if' (.send (some (.var .ivar x)) "is_a?" [.const cn] none) t (some el), .ifIsA y cn' dt de j =>
      if x != y || cn != cn' then none else
      match hx : ivarGet? I x with
      | some ρ =>
        if hg : ifIsAB κ ρ cn = true then
          match check n Γ t dt κ (ivarSet I x (isATy κ.classes κ.wholeCls cn ρ)) cache,
              check n Γ el de κ (ivarSet I x (notATy κ.classes κ.wholeCls cn ρ)) cache with
          | some ⟨τ₁, Γ₁, κ₁, I₁, ht, ct⟩, some ⟨τ₂, Γ₂, κ₂, I₂, he, ce⟩ =>
            if joinT τ₁ τ₂ == j && cacheSignaturesB ct ce then
              match ctxEq? κ₁ κ₂ with
              | some ⟨hctx⟩ =>
                if hi₁ : I₁ = ivarSet I x (isATy κ.classes κ.wholeCls cn ρ) then
                  if hi₂ : I₂ = ivarSet I x (notATy κ.classes κ.wholeCls cn ρ) then
                    some ⟨joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, κ₁, I,
                      .ifIsAIvar (used_0 := DJudge.rules ht) (used_1 := DJudge.rules he) hx hg (by simpa only [DJudge.rules, hi₁] using ht)
                        (by simpa only [DJudge.rules, hctx, hi₂] using he), ct⟩
                  else none
                else none
              | none => none
            else none
          | _, _ => none
        else none
      | none => none
    | .if' (.var .lvar x) _ (some e), .ifNilVar y de =>
      if x != y then none else
      match hx : envGet? Γ x with
      | some .nilT =>
        match check n Γ e de κ I cache with
        | some ⟨τ, Γ', κ', I', h, c⟩ => some ⟨τ, Γ', κ', I', .ifNilVar hx h, c⟩
        | none => none
      | _ => none
    | .casgn name e, .casgnTop de =>
      match check n Γ e de κ I cache with
      | some ⟨τ, Γ', κ', I', h, c⟩ =>
        if hg : casgnTopB κ' Γ' I' τ name = true then
          some ⟨τ, Γ', constAddCtx κ' name τ, I', .casgnTop h hg, c⟩
        else none
      | none => none
    | .const name, .constRead =>
      match hc : constGet? κ name with
      | some τ => some ⟨τ, Γ, κ, I, .constRead hc, cache⟩
      | none => none
    | .while' c b, .whileD dc db =>
      match check n Γ c dc κ I cache with
      | some ⟨_, Γc, κc, Ic, hc, cc⟩ =>
        if hΓc : Γc = Γ then
          match ctxEq? κc κ with
          | some ⟨hκc⟩ =>
            if hIc : Ic = I then
              match check n Γ b db κ I cc with
              | some ⟨_, Γb, κb, Ib, hb, cb⟩ =>
                if hΓb : Γb = Γ then
                  match ctxEq? κb κ with
                  | some ⟨hκb⟩ =>
                    if hIb : Ib = I then
                      some ⟨.nilT, Γ, κ, I, .while' (used_0 := DJudge.rules hc) (used_1 := DJudge.rules hb) (by subst hΓc hκc hIc; exact hc)
                        (by subst hΓb hκb hIb; exact hb), cb⟩
                    else none
                  | none => none
                else none
              | none => none
            else none
          | none => none
        else none
      | none => none
    | .if' c t none, .ifD dc dt none j =>
      match check n Γ c dc κ I cache with
      | some ⟨_, Γc, κc, Ic, hc, cc⟩ =>
        match check n Γc t dt κc Ic cc with
        | some ⟨τ, Γt, κt, It, ht, ct⟩ =>
          if joinT τ .nilT == j && cacheSignaturesB ct cc then
            match ctxEq? κt κc with
            | some ⟨hctx⟩ =>
              if hi : It = Ic then
                some ⟨joinT τ .nilT, joinEnv Γt Γc, κc, Ic,
                  .ifNoElse (used_0 := DJudge.rules hc) (used_1 := DJudge.rules ht) hc (by simpa only [DJudge.rules, hctx, hi] using ht), cc⟩
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
    | .def' name formals body, .defBlock name' ps bs br ret db => do
      if name != name' then none else do
      if hm : κ.scope.runtimeMain = true then do
      if hc : topDeclClassesB κ name = true then do
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
        match checkBoundCallbackBody n (topDeclCtx κ decl) I decl (.defBlock name' ps bs br ret db) with
        | some c =>
          some ⟨.sym, Γ, topDeclCtx κ decl, I,
            .defBoundBlock c.paramShape c.blockArgsFO c.blockReturnFO c.returnFO c.judged hm
              hc hs hb hco ha hi (List.all_eq_true.mp hg)
              (by simpa only [List.all_eq_true, bne_iff_ne] using hf) hmiss hquiet,
            { fresh with boundCallbacks := ⟨topDeclCtx κ decl, I, decl, c, db⟩ :: fresh.boundCallbacks }⟩
        | none => do
        let c ← checkCallbackBody n (topDeclCtx κ decl) I decl (.defBlock name' ps bs br ret db)
        some ⟨.sym, Γ, topDeclCtx κ decl, I,
          .defBlock c.paramShape c.paramsFO c.blockArgsFO c.blockReturnFO c.returnFO c.judged hm
            hc hs hb hco ha hi (List.all_eq_true.mp hg)
            (by simpa only [List.all_eq_true, bne_iff_ne] using hf) hmiss hquiet,
          { fresh with callbacks := ⟨topDeclCtx κ decl, I, decl, c, db⟩ :: fresh.callbacks }⟩
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
    | .def' name formals body, .defDeclRest name' ps o ret db => do
      if name != name' then none else do
      if κ.scope.runtimeClass.isSome then none else do
      if hshape : paramEqAll formals (ps.map (fun p => Param.req p.1) ++ [.rest (some o.1)]) = true then do
      if ht : ps.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then do
      if hσ : FirstOrder o.2 = true then do
      if hr : FirstOrder ret = true then do
      if hm : κ.scope.runtimeMain = true then do
      if hc : topDeclClassesB κ name = true then do
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
        match check n (ps ++ [(o.1, .arrayOf o.2)]) body db (topBodyCtx κ decl) I cache with
        | some ⟨τb, Γb, κb, Ib, hbj, _⟩ =>
          if hIb : Ib = I then
          if hτb : τb = ret then
          match ctxEq? κb (topBodyCtx κ decl) with
          | some ⟨hκb⟩ => do
            let fresh ← refreshBodies n (topDeclCtx κ decl) I cache
            some ⟨.sym, Γ, topDeclCtx κ decl, I,
              .defDeclRest (d := decl) (Γb := Γb) (paramEqAll_sound hshape)
                (by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using ht)
                hσ hr (by rw [hIb, hτb, hκb] at hbj; exact hbj)
                hm hc hs hb hco ha hi (List.all_eq_true.mp hg)
                (by simpa only [List.all_eq_true, bne_iff_ne] using hf) hmiss hquiet,
              fresh⟩
          | none => none
          else none
          else none
        | none => none
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
      else none
      else none
      else none
    | .def' name formals body, .defDeclKw name' ps ret db => do
      if name != name' then none else do
      if κ.scope.runtimeClass.isSome then none else do
      if hshape : paramEqAll formals (ps.map (fun p => Param.key p.1 none)) = true then do
      if ht : ps.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then do
      if hr : FirstOrder ret = true then do
      if hm : κ.scope.runtimeMain = true then do
      if hc : topDeclClassesB κ name = true then do
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
        match check n ps body db (topBodyCtx κ decl) I cache with
        | some ⟨τb, Γb, κb, Ib, hbj, _⟩ =>
          if hIb : Ib = I then
          if hτb : τb = ret then
          match ctxEq? κb (topBodyCtx κ decl) with
          | some ⟨hκb⟩ => do
            let fresh ← refreshBodies n (topDeclCtx κ decl) I cache
            some ⟨.sym, Γ, topDeclCtx κ decl, I,
              .defDeclKw (d := decl) (Γb := Γb) (paramEqAll_sound hshape)
                (by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using ht)
                hr (by rw [hIb, hτb, hκb] at hbj; exact hbj)
                hm hc hs hb hco ha hi (List.all_eq_true.mp hg)
                (by simpa only [List.all_eq_true, bne_iff_ne] using hf) hmiss hquiet,
              fresh⟩
          | none => none
          else none
          else none
        | none => none
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
      else none
      else none
    | .def' name formals body, .defDeclOpt name' ps o ddflt ret db => do
      if name != name' then none else do
      if κ.scope.runtimeClass.isSome then none else do
      let ⟨dflt, hshape⟩ ← optShape? formals ps o.1
      if ht : (ps ++ [(o.1, o.2)]).all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then do
      if hr : FirstOrder ret = true then do
      if hm : κ.scope.runtimeMain = true then do
      if hc : topDeclClassesB κ name = true then do
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
        match check n ps dflt ddflt (topBodyCtx κ decl) I cache with
        | some ⟨σd, Γd, κd, Id, hd, _⟩ =>
          if hΓd : Γd = ps then
          if hId : Id = I then
          if hσd : σd = o.2 then
          match ctxEq? κd (topBodyCtx κ decl) with
          | some ⟨hκd⟩ =>
            match check n (ps ++ [(o.1, o.2)]) body db (topBodyCtx κ decl) I cache with
            | some ⟨τb, Γb, κb, Ib, hbj, _⟩ =>
              if hIb : Ib = I then
              if hτb : τb = ret then
              match ctxEq? κb (topBodyCtx κ decl) with
              | some ⟨hκb⟩ => do
                let fresh ← refreshBodies n (topDeclCtx κ decl) I cache
                some ⟨.sym, Γ, topDeclCtx κ decl, I,
                  .defDeclOpt (d := decl) (σ := o.2) (Γb := Γb) (used_0 := DJudge.rules hd) (used_1 := DJudge.rules hbj) hshape
                    (by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using ht)
                    hr (by rw [hΓd, hId, hσd, hκd] at hd; exact hd) (by rw [hIb, hτb, hκb] at hbj; exact hbj)
                    hm hc hs hb hco ha hi (List.all_eq_true.mp hg)
                    (by simpa only [List.all_eq_true, bne_iff_ne] using hf) hmiss hquiet,
                  fresh⟩
              | none => none
              else none
              else none
            | none => none
          | none => none
          else none
          else none
          else none
        | none => none
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
      else none
    | .def' name formals body, .defDecl name' ps ret db => do
      if name != name' then none else do
      if let some cn := κ.scope.runtimeClass then
        checkMemberDefinition n κ Γ I cn ⟨name, formals, body⟩ (.defDecl name' ps ret db) cache
      else do
      if hm : κ.scope.runtimeMain = true then do
      if hc : topDeclClassesB κ name = true then do
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
            hc hs hb hco ha hi (List.all_eq_true.mp hg)
            (by simpa only [List.all_eq_true, bne_iff_ne] using hf) hmiss hquiet,
          { fresh with top := ⟨topBodyCtx κ decl, I, decl, c, db⟩ :: fresh.top }⟩
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
    | .send none name args none, .callSigRest name' ds ret ps o db => do
      if name != name' then none else do
      let a ← checkAll n Γ args ds κ I cache
      let ⟨decl, hdm, hname⟩ ← defnNamed? name a.ctx.defs
      let κb := a.ctx.withFrame (some ⟨"Object", "Object", decl.name, false⟩)
      if hshape : paramEqAll decl.params (ps.map (fun p => Param.req p.1) ++ [.rest (some o.1)]) = true then
      if htys : a.tys = ps.map (·.2) ++ List.replicate (a.tys.length - ps.length) o.2 then
      if ht : ps.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then
      if hσ : FirstOrder o.2 = true then
      if hr : FirstOrder ret = true then
      if hafter : envAfter ps o.1 (.arrayOf o.2) = ps ++ [(o.1, .arrayOf o.2)] then
      if hkill : killClosOverSpine a.spine o.1 (.arrayOf o.2) = a.spine then
      if hcap : capStale o.1 (.arrayOf o.2) (.arrayOf o.2) = false then
      if hctx : capStaleCtx o.1 (.arrayOf o.2) κb = false then
      if hstart : κ.scope.runtimeMain = true then
      if hm : a.ctx.scope.runtimeMain = true then
      if hs : a.ctx.selfTy = none then
      if hb : a.ctx.blockTy = none then
      if hco : a.ctx.consts = [] then
      if ha : a.ctx.asms = [] then
      if hi : FirstOrder a.spine = true then
      if hg : a.out.all (fun p => FirstOrder (stripAlias p.2)) = true then
        match check n (ps ++ [(o.1, .arrayOf o.2)]) decl.body db κb a.spine a.cache with
        | some ⟨τb, Γb, κb', Ib, hbj, _⟩ =>
          if hIb : Ib = a.spine then
          if hτb : τb = ret then
          match ctxEq? κb' κb with
          | some ⟨hκb⟩ =>
            some ⟨ret, a.out, a.ctx, a.spine, by
              simpa only [hname] using (DJudge.callSigRest (Γb := Γb) (paramEqAll_sound hshape)
                (by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using ht)
                hσ hr (by rw [hIb, hτb, hκb] at hbj; exact hbj)
                hafter hkill hcap hctx a.judged htys hdm hstart hm hs hb hco ha hi
                (List.all_eq_true.mp hg)), a.cache⟩
          | none => none
          else none
          else none
        | none => none
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
      else none
      else none
      else none
      else none
      else none
    | .send none name [.kwargs entries] none, .callSigKw name' ds ret ps db => do
      if name != name' then none else do
      match hka : kwArgs? (ps.map (·.1)) entries with
      | none => none
      | some args =>
      let a ← checkAll n Γ args ds κ I cache
      let ⟨decl, hdm, hname⟩ ← defnNamed? name a.ctx.defs
      let κb := a.ctx.withFrame (some ⟨"Object", "Object", decl.name, false⟩)
      if hshape : paramEqAll decl.params (ps.map (fun p => Param.key p.1 none)) = true then
      if htys : a.tys = ps.map (·.2) then
      if hnd : (ps.map (·.1)).Nodup then
      if hne : ps ≠ [] then
      if ht : ps.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then
      if hr : FirstOrder ret = true then
      if hstart : κ.scope.runtimeMain = true then
      if hm : a.ctx.scope.runtimeMain = true then
      if hs : a.ctx.selfTy = none then
      if hb : a.ctx.blockTy = none then
      if hco : a.ctx.consts = [] then
      if ha : a.ctx.asms = [] then
      if hi : FirstOrder a.spine = true then
      if hg : a.out.all (fun p => FirstOrder (stripAlias p.2)) = true then
        match check n ps decl.body db κb a.spine a.cache with
        | some ⟨τb, Γb, κb', Ib, hbj, _⟩ =>
          if hIb : Ib = a.spine then
          if hτb : τb = ret then
          match ctxEq? κb' κb with
          | some ⟨hκb⟩ =>
            some ⟨ret, a.out, a.ctx, a.spine, by
              simpa only [hname] using (DJudge.callSigKw (Γb := Γb) (paramEqAll_sound hshape)
                hnd hne hka
                (by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using ht)
                hr (by rw [hIb, hτb, hκb] at hbj; exact hbj)
                (by rw [← htys]; exact a.judged) hdm hstart hm hs hb hco ha hi
                (List.all_eq_true.mp hg)), a.cache⟩
          | none => none
          else none
          else none
        | none => none
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
      else none
      else none
    | .send none name args none, .callSigOpt name' ds ret ps o ddflt db => do
      if name != name' then none else do
      let a ← checkAll n Γ args ds κ I cache
      let ⟨decl, hdm, hname⟩ ← defnNamed? name a.ctx.defs
      let ⟨dflt, hshape⟩ ← optShape? decl.params ps o.1
      let κb := a.ctx.withFrame (some ⟨"Object", "Object", decl.name, false⟩)
      if htys : a.tys = ps.map (·.2) ∨ a.tys = (ps ++ [(o.1, o.2)]).map (·.2) then
      if ht : (ps ++ [(o.1, o.2)]).all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then
      if hr : FirstOrder ret = true then
      if hafter : envAfter ps o.1 o.2 = ps ++ [(o.1, o.2)] then
      if hkill : killClosOverSpine a.spine o.1 o.2 = a.spine then
      if hcap : capStale o.1 o.2 o.2 = false then
      if hctx : capStaleCtx o.1 o.2 κb = false then
      if hstart : κ.scope.runtimeMain = true then
      if hm : a.ctx.scope.runtimeMain = true then
      if hs : a.ctx.selfTy = none then
      if hb : a.ctx.blockTy = none then
      if hco : a.ctx.consts = [] then
      if ha : a.ctx.asms = [] then
      if hi : FirstOrder a.spine = true then
      if hg : a.out.all (fun p => FirstOrder (stripAlias p.2)) = true then
        match check n ps dflt ddflt κb a.spine a.cache with
        | some ⟨σd, Γd, κd, Id, hd, _⟩ =>
          if hΓd : Γd = ps then
          if hId : Id = a.spine then
          if hσd : σd = o.2 then
          match ctxEq? κd κb with
          | some ⟨hκd⟩ =>
            match check n (ps ++ [(o.1, o.2)]) decl.body db κb a.spine a.cache with
            | some ⟨τb, Γb, κb', Ib, hbj, _⟩ =>
              if hIb : Ib = a.spine then
              if hτb : τb = ret then
              match ctxEq? κb' κb with
              | some ⟨hκb⟩ =>
                some ⟨ret, a.out, a.ctx, a.spine, by
                  simpa only [hname] using (DJudge.callSigOpt (σ := o.2) (Γb := Γb) (used_0 := DJudge.rules hd) (used_1 := DJudge.rules hbj) hshape
                    (by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using ht)
                    hr (by rw [hΓd, hId, hσd, hκd] at hd; exact hd) (by rw [hIb, hτb, hκb] at hbj; exact hbj)
                    hafter hkill hcap hctx a.judged htys hdm hstart hm hs hb hco ha hi
                    (List.all_eq_true.mp hg)), a.cache⟩
              | none => none
              else none
              else none
            | none => none
          | none => none
          else none
          else none
          else none
        | none => none
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
      else none
      else none
      else none
    | .send none name args none, .callSig name' ds ret => do
      if name != name' then none else do
      match κ.selfTy with
      | some (.clsOf _) =>
        checkImplicitSingleton n Γ (.send none name args none) name args ds ret .send κ I cache
      | _ => do
        let a ← checkAll n Γ args ds κ I cache
        let c ← findBody a.ctx a.spine name a.cache.top
        if ht : a.tys = c.body.params.map (·.2) then do
        let result ← c.body.resultAt ret
        if hstart : κ.scope.runtimeMain = true then do
        if hm : a.ctx.scope.runtimeMain = true then do
        if hs : a.ctx.selfTy = none then do
        if hb : a.ctx.blockTy = none then do
        if hco : a.ctx.consts = [] then do
        if ha : a.ctx.asms = [] then do
        if hi : FirstOrder a.spine = true then do
        if hg : a.out.all (fun p => FirstOrder (stripAlias p.2)) = true then
          some ⟨ret, a.out, a.ctx, a.spine, by
            simpa only [c.nameOk] using
              (DJudge.callSig c.body.paramShape c.body.paramsFO result.firstOrder result.judged
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
    | _, _ => none

/-- Reuse only an exact-context checked own singleton body. The syntax guard keeps
bare calls distinct from implicit sends while both retain the incoming self receiver. -/
def checkImplicitSingleton (fuel : Nat) (Γ : Env) (call : Expr) (name : String)
    (args : List Expr) (ds : List Deriv) (ret : Ty) (shape : ImplicitCallShape call name args)
    (κ : Ctx) (I : Ty) (cache : CheckedCache) : Option (Certified Γ call κ I) :=
  match fuel with
  | 0 => none
  | n + 1 => do
    match hs : κ.selfTy with
    | some (.clsOf cn) => do
      let a ← checkAll n Γ args ds κ I cache
      let f ← findClass cn a.ctx.classes
      let c ← findSingleton a.ctx f.cls name a.cache.singletons
      if ht : a.tys = c.body.params.map (·.2) then do
      let result ← c.body.resultAt ret
      if hn : directCallNameB c.decl.name = true then do
      if hg : instanceCallB a.ctx a.out a.spine = true then
        some ⟨ret, a.out, a.ctx, a.spine,
          DJudge.callSingletonImplicit (by simpa only [c.nameOk] using shape)
            (by simpa only [f.nameOk] using hs) (by simpa only [ht] using a.judged)
            f.member c.installed hn c.body.paramShape c.body.paramsFO
            result.firstOrder result.judged hg, a.cache⟩
      else none
      else none
      else none
    | _ => none

def checkAll (fuel : Nat) (Γ : Env) (es : List Expr) (ds : List Deriv)
    (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : CheckedCache := {}) : Option (CertifiedAll Γ es κ I) :=
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
    (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : CheckedCache := {}) : Option (CertifiedPairs Γ ps κ I) :=
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
    (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : CheckedCache := {}) : Option (CertifiedSeq Γ es κ I) :=
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
argument values are deliberately not inputs. Return compatibility is equality or the
proved same-class instance-to-nominal conversion; annotations themselves stay unchanged. -/
def checkMethodBody (fuel : Nat) (κ : Ctx) (I : Ty) (decl : Defn) (d : Deriv)
    (cache : CheckedCache := {}) : Option (CheckedBody κ I decl) :=
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
          let raw := c
          let refined : Option ((ty : Ty) × CheckedResult κ I decl ps ty) := do
            if hfo : FirstOrder raw.ty = true then do
              let ⟨hc⟩ ← ctxEq? raw.ctx κ
              if hi : raw.spine = I then
                some ⟨raw.ty, raw.out, hfo, by simpa only [hc, hi] using raw.judged⟩
              else none
            else none
          let c ← checkResult c ret
          if hret : c.ty = ret then do
            let ⟨hctx⟩ ← ctxEq? c.ctx κ
            if hspine : c.spine = I then
              some ⟨ps, ret, c.out, paramEqAll_sound hp,
                by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using ht,
                hr, by simpa only [hret, hctx, hspine] using c.judged, refined⟩
            else none
          else none
        else none
      else none
    else none
  | _ => none

/-- Definition admission is annotation-domain checking, including uncalled members.
The current initializer's proved output supplies self fields; it is never a call argument. -/
def checkMemberDefinition (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty) (cn : String)
    (d : Defn) (hint : Deriv) (cache : CheckedCache) :
    Option (Certified Γ (.def' d.name d.params d.body) κ I) :=
  match fuel with
  | 0 => none
  | n + 1 => do
    let f ← findClass cn κ.classes
    if hg : memberRuleB κ Γ I f.cls d = true then do
    let next := instanceDeclCtx κ f.cls d
    let .defDecl _ _ _ db := hint | none
    if hn : d.name = "initialize" then do
      let body ← checkInitializerBody n (initializerBodyCtx next f.cls.name) d hint (initializerSources cache)
      let fresh ← refreshClassBodies n next { cache with initializers :=
        ⟨initializerBodyCtx next f.cls.name, f.cls.name, f.cls.name, d, body, db⟩ :: cache.initializers }
      if receiverCacheCompleteB next fresh then
        some ⟨.sym, Γ, next, I,
        .initDef hn body.paramShape body.paramsFO body.returnFO body.fieldsFO body.judged f.member hg, fresh⟩
      else none
    else do
      let fresh ← refreshClassBodies n next cache
      let fields := receiverFields next (classWithMethod f.cls d) fresh
      if hf : FirstOrder fields = true then do
        let bctx := instanceBodyCtx next ⟨f.cls.name, f.cls.name, d.name, false⟩ fields
        let body ← checkMethodBody n bctx fields d hint fresh
        let variants ← refreshMemberReceivers n next fresh
          ⟨⟨bctx, fields, d, body, db⟩, f.cls.name, f.cls.name⟩ (next.classes.map (·.name)).eraseDups
        let complete := { fresh with members := variants ++ fresh.members }
        if receiverCacheCompleteB next complete then
          some ⟨.sym, Γ, next, I,
          .memberDef body.paramShape body.paramsFO body.returnFO hf body.judged hn f.member hg,
          complete⟩
        else none
      else none
    else none

/-- Def-self uses annotations alone, including when the method is never called. -/
def checkSingletonDefinition (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty) (cn : String)
    (d : Defn) (hint : Deriv) (cache : CheckedCache) :
    Option (Certified Γ (.defs .self' d.name d.params d.body) κ I) :=
  match fuel with
  | 0 => none
  | n + 1 => do
    let f ← findClass cn κ.classes
    if hg : singletonRuleB κ Γ I f.cls d = true then do
      let next := singletonDeclCtx κ f.cls d
      let .defDecl _ _ _ db := hint | none
      let fresh ← refreshClassBodies n next cache
      let bctx := singletonBodyCtx next f.cls.name d.name
      let body ← checkMethodBody n bctx .ivar0 d hint fresh
      let complete := { fresh with singletons :=
        ⟨⟨bctx, .ivar0, d, body, db⟩, f.cls.name⟩ :: fresh.singletons }
      if receiverCacheCompleteB next complete && singletonCacheCompleteB next complete then
        some ⟨.sym, Γ, next, I,
          .singletonDef body.paramShape body.paramsFO body.returnFO body.judged f.member hg, complete⟩
      else none
    else none

/-- Scoped recursion is a fallback for nodes containing a self-call. Closed subtrees keep
their ordinary derivations; the scope is never inserted into the checked-body cache. -/
def checkRec (fuel : Nat) (κ : Ctx) (I : Ty) (s : RecScope) (Γ : Env)
    (e : Expr) (d : Deriv) (cache : CheckedCache) : Option (CertifiedRec κ I s Γ e) :=
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
        let ⟨hframe⟩ ← ctxEq? (κ.withFrame (some ⟨"Object", "Object", s.decl.name, false⟩)) κ
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
    (es : List Expr) (ds : List Deriv) (cache : CheckedCache) : Option (CertifiedRecAll κ I s Γ es) :=
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
def refreshTopBodies (fuel : Nat) (κ : Ctx) (I : Ty) (base : CheckedCache)
    (cache : BodyCache) : Option BodyCache :=
  match fuel with
  | 0 => none
  | n + 1 => match cache with
    | [] => some []
    | c :: cs => do
      let fresh ← refreshTopBodies n κ I base cs
      let bodyCtx := κ.withFrame (some ⟨"Object", "Object", c.decl.name, false⟩)
      let body ← checkMethodBody n bodyCtx I c.decl
        (.defDecl c.decl.name c.body.params c.body.ret c.deriv) { base with top := fresh }
      some (⟨bodyCtx, I, c.decl, body, c.deriv⟩ :: fresh)

/-- Rebuild a source initializer at every receiver where ordered lookup selects it.
An inapplicable owner is skipped; every applicable replay failure propagates. -/
def refreshInitializerReceivers (fuel : Nat) (κ : Ctx) (c : CachedInitializer) (names : List String)
    (sources : List InitializerSource := []) :
    Option (List CachedInitializer) :=
  match fuel with
  | 0 => none
  | n + 1 => match names with
    | [] => some []
    | cn :: names => do
      let tail ← refreshInitializerReceivers n κ c names sources
      match memberRoute? κ.classes cn c.owner c.decl with
      | none => some tail
      | some _ => do
        let ctx := initializerBodyCtxAt κ cn c.owner
        let body ← refreshInitializerBody n ctx c.body c.deriv sources
        some (⟨ctx, c.owner, cn, c.decl, body, c.deriv⟩ :: tail)

/-- Initializers for every receiver precede members: their proved fields type self. -/
def refreshInitializers (fuel : Nat) (κ : Ctx) (cache : List CachedInitializer)
    (sources : List InitializerSource := []) :
    Option (List CachedInitializer) :=
  match fuel with
  | 0 => none
  | n + 1 => match cache with
    | [] => some []
    | c :: cs => do
      let _ ← memberRoute? κ.classes c.owner c.owner c.decl
      let bodies ← refreshInitializerReceivers n κ c (κ.classes.map (·.name)).eraseDups sources
      let tail ← refreshInitializers n κ cs sources
      some (bodies ++ tail)

def refreshMemberReceivers (fuel : Nat) (κ : Ctx) (base : CheckedCache) (c : CachedMember)
    (names : List String) : Option (List CachedMember) :=
  match fuel with
  | 0 => none
  | n + 1 => match names with
    | [] => some []
    | cn :: names => do
      let tail ← refreshMemberReceivers n κ base c names
      match memberRoute? κ.classes cn c.owner c.decl with
      | none => some tail
      | some _ => do
        let f ← findClass cn κ.classes
        let fields := receiverFields κ f.cls base
        let ctx := instanceBodyCtx κ ⟨cn, c.owner, c.decl.name, false⟩ fields
        let body ← checkMethodBody n ctx fields c.decl
          (.defDecl c.decl.name c.body.params c.body.ret c.deriv) base
        some (⟨⟨ctx, fields, c.decl, body, c.deriv⟩, c.owner, cn⟩ :: tail)

/-- Oldest source first, each expanded at all effective receivers. Earlier annotation
proofs are dependencies; neither call values nor receiver-specialized signatures enter. -/
def refreshMembers (fuel : Nat) (κ : Ctx) (base : CheckedCache) (cache : List CachedMember) :
    Option (List CachedMember) :=
  match fuel with
  | 0 => none
  | n + 1 => match cache with
    | [] => some []
    | c :: cs => do
      let tail ← refreshMembers n κ base cs
      let _ ← memberRoute? κ.classes c.owner c.owner c.decl
      let bodies ← refreshMemberReceivers n κ { base with members := tail } c
        (κ.classes.map (·.name)).eraseDups
      some (bodies ++ tail)

/-- Oldest own singleton first; replay keeps the original annotations at the new tables. -/
def refreshSingletons (fuel : Nat) (κ : Ctx) (base : CheckedCache) (cache : List CachedSingleton) :
    Option (List CachedSingleton) :=
  match fuel with
  | 0 => none
  | n + 1 => match cache with
    | [] => some []
    | c :: cs => do
      let tail ← refreshSingletons n κ base cs
      let f ← findClass c.owner κ.classes
      let _ ← defnMem? c.decl f.cls.smethods
      let bctx := singletonBodyCtx κ c.owner c.decl.name
      let body ← checkMethodBody n bctx .ivar0 c.decl
        (.defDecl c.decl.name c.body.params c.body.ret c.deriv) { base with singletons := tail }
      some (⟨⟨bctx, .ivar0, c.decl, body, c.deriv⟩, c.owner⟩ :: tail)

/-- Class bodies cannot call top-level methods. Keep those artifacts until class exit,
where refreshBodies rechecks them in the restored caller scope, even if never called. -/
def refreshClassBodies (fuel : Nat) (κ : Ctx) (cache : CheckedCache) : Option CheckedCache :=
  match fuel with
  | 0 => none
  | n + 1 => do
    let is ← refreshInitializers n κ (cache.initializers.filter fun c => c.receiver == c.owner) (initializerSources cache)
    let ms ← refreshMembers n κ { cache with initializers := is } (cache.members.filter fun c => c.receiver == c.owner)
    let base := { cache with initializers := is, members := ms }
    let ss ← refreshSingletons n κ base cache.singletons
    some { base with singletons := ss }

def refreshBodies (fuel : Nat) (κ : Ctx) (I : Ty) (cache : CheckedCache) : Option CheckedCache :=
  match fuel with
  | 0 => none
  | n + 1 => do
    let base ← refreshClassBodies n κ cache
    let ts ← refreshTopBodies n κ I base cache.top
    let callbacks ← refreshCallbackBodies n κ I cache.callbacks
    let boundCallbacks ← refreshBoundCallbackBodies n κ I cache.boundCallbacks
    let complete := { base with top := ts, callbacks := callbacks, boundCallbacks := boundCallbacks }
    if receiverCacheCompleteB κ complete && singletonCacheCompleteB κ complete then some complete else none
end

end Ratchet.Audit
