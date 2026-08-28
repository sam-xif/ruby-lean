import RubyCore.Cert.CheckAux

/-!
# `chk` — the certificate checker, over the whole `Expr` grammar

`docs/semantics/certificate-language.md` §4 D1 (stackmaps, C5), D2a (per-site
instantiations, C6), §8 risk 1 (kernel replay cost) — and the thing all three were
waiting on, which is a checker that is **not** `infer`.

## Why this file exists

C0–C4's `validate` had a conjunct named `nominalOk`, and `nominalOk` was
`(infer (c.table p) [] p true …).isSome`. Two consequences, recorded as §9.1 and
§9.3 of the design document, and they are the two things this file is answering:

1. **Coverage was `infer`'s coverage.** A certificate could name a *table* and
   nothing else, so §9.1's honest half — *"a certificate cannot say anything the
   nominal judgement cannot check"* — bounded the fourth ratchet at whatever
   `infer`'s ~30 arms admit. Nine `Expr` heads had no arm at all (`begin'`,
   `hash`, `for'`, `defined`, `module'`, …), and no certificate could reach them.
2. **The checked path did not reduce.** `infer` is well-founded-recursive, so
   kernel reduction gets stuck on it, so four of C0's six conjuncts `decide`d and
   two were discharged by `simp` over equation lemmas. §8 risk 1 prescribes the fix
   — *reduction-friendly validator data structures, never `native_decide`* — and
   says it is a restructuring of `Types/Core.lean`, which §7 norm 7 puts out of
   scope.

**Both are fixed here, and neither needed `Types/Core.lean` touched**, because the
fix is not to restructure `infer` — it is to stop calling it. `chk` is a *new*
checker, in `Cert/`, where norm 7 says this initiative's trusted code belongs:

* **structurally recursive on fuel** (V9), so it reduces in the kernel and
  `validate` is one `decide`;
* **total over the grammar** (V10) — an arm for every one of the 47 `Expr`
  constructors, so there is no head a certificate cannot address;
* **certificate-driven at every choice** (V11) — where the deterministic rule has
  no answer, the certificate supplies one and `chk` checks the *consequences* of
  it rather than searching.

## The two tiers, and why the file says so in its types

Coverage and soundness are now different numbers, and pretending otherwise would be
the one failure mode §8 risk 3 names. So:

| tier | predicate | what it buys |
|---|---|---|
| **sound** | `validate c p && inferFrag p && c.claimFree` | `validate_sound` — no reachable `typeStuck`, conditional on the printed residue |
| **covered** | `validate c p` | the fourth ratchet: this body checked, at this table, with these claims |

`inferFrag` (§5) is the syntactic predicate marking the sub-grammar on which
`chk_infer` (`Proof/Cert/Check.lean`) proves `chk` accepts only where `infer`
does — and it is *exactly* `infer`'s own domain, because that is where the existing
`Inv` can carry the accept. **The rest of the grammar is checked and not yet
certified**, and the reason is the schema wall §8 risk 2 predicted: `CtlOk`'s eval
clause is stated in terms of `infer`, so a `begin`/`rescue` accept needs a
preservation case in `Proof/Static/Preservation.lean` and not a validator arm.
Growing `inferFrag` is that work, one head at a time, and it is the *only* thing
between the covered tier and the sound one. Flagged in the design document's §10
rather than buried here, because it is a change to what an accept means.

## The shape of a rule

Every arm is one of three shapes, and which one it is is the whole information
content of the arm:

* **derived** — the type follows from the children (`.int`, `.array`, `.seq`);
* **declared** — the type is read out of the table (`.send`, `.const`, `.var .ivar`);
* **claimed** — the certificate says, and `chk` checks what follows
  (`.if'` at a join the deterministic `joinTy` refuses, `.def'` with parameters).

A claim is consulted **only in the `none` branch** of the deterministic rule. That
is a deliberate ordering and it is load-bearing: a claim can never *override* a rule
that fired and refused, so a wrong claim costs a body and cannot buy an accept. It
is `deltaRows`' bargain (§1: *"a bad certificate costs a body we failed to certify —
never a false type-checked"*) applied per node.
-/

namespace RubyCore.Cert

open RubyCore.Types


/-! ## 2. `chk` and the functions it is mutual with

One `match` on the head, in the order the grammar declares them, so that a missing
arm is visible as a gap in the reading rather than swallowed by a catch-all. **There
is no catch-all**: that is V10, and it is the difference between this function and
`infer`'s trailing `| _ => none`.

**There is no path parameter** (V15). A claim is looked up by the *subterm* it is
about, so `chk`'s signature is `infer`'s plus the certificate and the fuel — which is
what lets the soundness argument state it at a machine, and what deletes the emitter's
obligation to compute addresses the same way the checker does. `Cert/Json.lean` still
speaks `Path` on the wire and resolves it on load. -/

/-- The claimed type of a node, or `none`. Local abbreviation for the pattern every
    fallback branch uses. -/
def claimTy (c : Cert) (e : Expr) : Option Ty := (c.claimAt e).map (·.ty)

/-- The claimed continuation environment of a node, defaulting to the one passed in
    — which is what every deterministic arm wants. -/
def claimEnv (c : Cert) (e : Expr) (Γ : Env) : Env :=
  match c.claimAt e with
  | some cl => cl.env.getD Γ
  | none => Γ

/-- The claimed type list at a node (declared parameters, or a call-site
    instantiation), or `[]`. -/
def claimTys (c : Cert) (e : Expr) : List Ty :=
  match c.claimAt e with
  | some cl => cl.tys.getD []
  | none => []


mutual

/-- **An optional subterm**, checked if present; `nil` and the incoming environment and
    table if absent.

    It exists for the metatheory rather than for brevity. An *inline* `match eo with …`
    inside an arm of `chk` becomes, after `split at h`, a hypothesis whose scrutinee is
    still `eo`, and `split at h` cannot reach inside a hypothesis it just created. In
    the arms whose enclosing pattern is a wildcard — a send whose block is `some val`
    for an unconstrained `val` — there is then no way to make `eo` concrete and the
    case is unprovable without restructuring. Naming the computation turns it into a
    function application that a *law* can consume. -/
def chkOpt (c : Cert) : Nat → Decls → Env → Option Expr → Bool → FrameCtx →
    Option (Ty × Env × Decls)
  | _, D, Γ, none, _, _ => some (.nilT, Γ, D)
  | 0, _, _, _, _, _ => none
  | n + 1, D, Γ, some e, top, ctx => chk c n D Γ e top ctx

/-- **The receiver of a send.** An explicit receiver is checked; an implicit one is
    `self`, which has a type only where it is an *instance* — in a class body it is the
    class object, which `plainRecv` excludes.

    Named for `chkOpt`'s reason (V19): inline, the `match recvO with …` becomes a case
    hypothesis of `chk.induct` whose scrutinee is still `recvO`, and there is then no
    way to make it concrete — the send arm was the last thing blocking the
    table-return law. Named, it gets a motive of its own and the induction hypothesis
    covers it. -/
def chkRecv (c : Cert) : Nat → Decls → Env → Option Expr → Bool → FrameCtx →
    Option (Ty × Env × Decls)
  | _, D, Γ, none, _, ctx =>
    match ctx.selfCls with
    | some cc => some (.cls cc, Γ, D)
    | none => none
  | 0, _, _, _, _, _ => none
  | n + 1, D, Γ, some r, top, ctx => chk c n D Γ r top ctx

/-- A statement sequence: thread the environment and the table, take the last type.
    An empty sequence is `nil`, and `[e]` is `e` — the three-way split `evalExpr` makes
    on `.seq`. -/
def chkSeq (c : Cert) : Nat → Bool → FrameCtx → Decls → Env → List Expr →
    Option (Ty × Env × Decls)
  | _, _, _, D, Γ, [] => some (.nilT, Γ, D)
  | 0, _, _, _, _, _ => none
  | n + 1, top, ctx, D, Γ, [e] => chk c n D Γ e top ctx
  | n + 1, top, ctx, D, Γ, e :: rest =>
    match chk c n D Γ e top ctx with
    | some (_, Γ₁, D₁) => chkSeq c n top ctx D₁ Γ₁ rest
    | none => none

/-- An argument list: the same threading, but the *types* are kept in order, because
    that is what a signature's parameter list is matched against. -/
def chkArgs (c : Cert) : Nat → Bool → FrameCtx → Decls → Env → List Expr →
    Option (List Ty × Env × Decls)
  | _, _, _, D, Γ, [] => some ([], Γ, D)
  | 0, _, _, _, _, _ => none
  | n + 1, top, ctx, D, Γ, e :: rest =>
    match chk c n D Γ e top ctx with
    | some (τ, Γ₁, D₁) =>
      match chkArgs c n top ctx D₁ Γ₁ rest with
      | some (τs, Γ₂, D₂) => some (τ :: τs, Γ₂, D₂)
      | none => none
    | none => none

/-- The elements of an array literal. Element types are erased (`.array` answers
    `.cls "Array"`), and a `.splat` element's operand must be exactly `Array` — which
    is what makes the step total, since `spreadA` errors on any other payload. -/
def chkElems (c : Cert) : Nat → Bool → FrameCtx → Decls → Env → List Expr →
    Option (Ty × Env × Decls)
  | _, _, _, D, Γ, [] => some (.nilT, Γ, D)
  | 0, _, _, _, _, _ => none
  | n + 1, top, ctx, D, Γ, e :: rest =>
    match e with
    | .splat (some o) =>
      match chk c n D Γ o top ctx with
      | some (.cls "Array", Γ₁, D₁) => chkElems c n top ctx D₁ Γ₁ rest
      | _ => none
    | ee =>
      match chk c n D Γ ee top ctx with
      | some (_, Γ₁, D₁) => chkElems c n top ctx D₁ Γ₁ rest
      | none => none

/-- The pairs of a hash literal — key then value, left to right, threading both. -/
def chkPairs (c : Cert) : Nat → Bool → FrameCtx → Decls → Env →
    List (Expr × Expr) → Option (Env × Decls)
  | _, _, _, D, Γ, [] => some (Γ, D)
  | 0, _, _, _, _, _ => none
  | n + 1, top, ctx, D, Γ, (k, v) :: rest =>
    match chk c n D Γ k top ctx with
    | some (_, Γ₁, D₁) =>
      match chk c n D₁ Γ₁ v top ctx with
      | some (_, Γ₂, D₂) => chkPairs c n top ctx D₂ Γ₂ rest
      | none => none
    | none => none

/-- The entries of a brace-less keyword-argument marker. Each entry's *value* is
    evaluated; a `.dyn` entry's key is too. -/
def chkKwEntries (c : Cert) : Nat → Bool → FrameCtx → Decls → Env → List KwEntry →
    Option (Env × Decls)
  | _, _, _, D, Γ, [] => some (Γ, D)
  | 0, _, _, _, _, _ => none
  | n + 1, top, ctx, D, Γ, ent :: rest =>
    match ent with
    | .pair _ v =>
      match chk c n D Γ v top ctx with
      | some (_, Γ₁, D₁) => chkKwEntries c n top ctx D₁ Γ₁ rest
      | none => none
    | .splat v =>
      match chk c n D Γ v top ctx with
      | some (_, Γ₁, D₁) => chkKwEntries c n top ctx D₁ Γ₁ rest
      | none => none
    | .dyn k v =>
      match chk c n D Γ k top ctx with
      | some (_, Γ₁, D₁) =>
        match chk c n D₁ Γ₁ v top ctx with
        | some (_, Γ₂, D₂) => chkKwEntries c n top ctx D₂ Γ₂ rest
        | none => none
      | none => none

/-- The handlers of a `begin` region: each is checked at the **entry** environment,
    because a handler may run after any prefix of the body and nothing the body bound
    is guaranteed. The exception-class list is checked as an ordinary expression list
    (each entry is a constant read); the target binds the exception, at the claimed
    type or at the first class named. -/
def chkRescues (c : Cert) : Nat → Bool → FrameCtx → Decls → Env →
    List (List Expr × Option (TargetKind × String) × Expr) → Option (List Ty)
  | _, _, _, _, _, [] => some []
  | 0, _, _, _, _, _ => none
  | n + 1, top, ctx, D, Γ, (excs, tgt, hbody) :: rest =>
    match chkArgs c n top ctx D Γ excs with
    | none => none
    | some (τs, _, D₁) =>
      if D₁ != D then none
      else
        -- The bound exception's type: the claim if there is one, else the sole
        -- class named (`rescue Foo => e` with one class is the common shape), else
        -- `.any`, which is honest — a handler that dispatches on a multi-class
        -- binding needs the union `Ty` does not have (§9.8).
        let τx := match (c.claimAt hbody).bind (·.tys) with
          | some (τ :: _) => τ
          | _ => match τs with
            | [.clsOf n] => .cls n
            | _ => .any
        let Γh := match tgt with
          | some (_, x) => envSet Γ x τx
          | none => Γ
        match chk c n D Γh hbody top ctx with
        | none => none
        | some (τh, _, Dh) =>
          if Dh != D then none
          else
            match chkRescues c n top ctx D Γ rest with
            | some τrs => some (τh :: τrs)
            | none => none

/-- A block send whose row `blockSend?`/`blockSendA?` does not supply — the claimed
    arm. The block's body is still **checked**, at the claimed parameter type, so
    what the certificate supplies is the row and not the body's typing. -/
def chkBlockClaim (c : Cert) : Nat → Bool → FrameCtx → Expr → Decls → Env →
    List Ty → List Param → List String → Expr → Option (Ty × Env × Decls)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, _top, ctx, key, D, Γ, τs, ps, ls, body =>
  let _ := ls
  let _ := τs
  match c.claimAt key with
  | none => none
  | some cl =>
    let τp := match cl.tys with
      | some (τ :: _) => τ
      | _ => .any
    let Γb := bindParams n ps [τp] (anyEnv Γ)
    match chk c n D Γb body false (blockCtx ctx) with
    | some (_, _, D') => if D' == D && ctx.inBlock == false then some (cl.ty, Γ, D) else none
    | none => none

/-- **The checker.** `chk c n D Γ e top ctx = some (τ, Γ', D')` — at the
    certificate `c`, with `n` fuel, `e` has type `τ` and leaves the environment `Γ'`
    and the table `D'` in force. `none` is a refusal: ill-typed, unclaimed where a
    claim was needed, or out of fuel.

    The parameters other than `c` and `n` are `infer`'s, unchanged and for
    `infer`'s reasons — see `Types/Core.lean` for `top` (the toplevel-position flag
    `class'` needs) and `Types/Ty.lean` for `FrameCtx`'s six channels. Reusing them
    rather than inventing a context is what makes `chk_infer` a statement about two
    functions with the same signature. -/
def chk (c : Cert) : Nat → Decls → Env → Expr → Bool → FrameCtx →
    Option (Ty × Env × Decls)
  | 0, _, _, _, _, _ => none
  | n + 1, D, Γ, e, top, ctx =>
    match e with
    -- ## Literals — derived, immediate, and each one `evalExpr`'s own answer.
    | .int _ => some (.int, Γ, D)
    | .flt _ => some (.float, Γ, D)
    | .regexpLit _ _ => none
    | .str _ => some (.cls "String", Γ, D)
    | .sym _ => some (.sym, Γ, D)
    | .tru => some (.bool, Γ, D)
    | .fls => some (.bool, Γ, D)
    | .nil => some (.nilT, Γ, D)
    -- `self` has a type only where it is an *instance*; in a class body it is the
    -- class object, which `plainRecv` excludes and `valueTy?` gives no type at all.
    | .self' =>
      match ctx.selfCls with
      | some cc => some (.cls cc, Γ, D)
      | none => none
    -- ## Variables.
    | .var .lvar x => (envGet? Γ x).map (fun τ => (τ, Γ, D))
    | .var .ivar x =>
      match ctx.selfCls with
      | some cc =>
        match ivarTy? D cc x with
        | some σ => some (mkNilable σ, Γ, D)
        | none => none
      | none => none
    | .var .gvar x =>
      match plainGlobal x, globalTy? D x with
      | true, some σ => some (mkNilable σ, Γ, D)
      | _, _ => none
    -- **A class variable has no declaration channel** — `Decls` has `ivars`,
    -- `globals` and `consts` and nothing keyed on a cvar — so this is the first arm
    -- whose *only* source of a type is the certificate. A `cvarTy?` field would be a
    -- `Types/Decls.lean` change, which norm 7 keeps out of this initiative; a claim
    -- is the same information with the trust visible.
    | .var .cvar _ =>
      match claimTy c e with
      | some τ => some (mkNilable τ, Γ, D)
      | none => none
    -- ## Assignment. The local case refuses inside a block, because a block body's
    -- assignment to an *enclosing* local is a write the block frame's
    -- `FrameConforms` obligation cannot see (L252).
    | .vasgn .lvar x rhs =>
      match ctx.inBlock with
      | true => none
      | false =>
        match chk c n D Γ rhs top ctx with
        | some (τ, Γ₁, D₁) => some (τ, envSet Γ₁ x τ, D₁)
        | none => none
    | .vasgn .ivar x rhs =>
      match ctx.selfCls with
      | some cc =>
        match chk c n D Γ rhs top ctx with
        | some (τ, Γ₁, D₁) =>
          match ivarTy? D₁ cc x with
          | some σ => if subTy τ σ then some (τ, Γ₁, D₁) else none
          | none => some (τ, Γ₁, D₁)
        | none => none
      | none => none
    | .vasgn .gvar x rhs =>
      match plainGlobal x with
      | true =>
        match chk c n D Γ rhs top ctx with
        | some (τ, Γ₁, D₁) =>
          match globalTy? D₁ x with
          | some σ => if subTy τ σ then some (τ, Γ₁, D₁) else none
          | none => none
        | none => none
      | false => none
    -- A cvar write is checked against the claim if there is one, and otherwise just
    -- answers the right-hand side's type: the *read* is what needs a declaration.
    | .vasgn .cvar _ rhs =>
      match chk c n D Γ rhs top ctx with
      | some (τ, Γ₁, D₁) =>
        match claimTy c e with
        | some σ => if subTy τ σ then some (τ, Γ₁, D₁) else none
        | none => some (τ, Γ₁, D₁)
      | none => none
    -- ## Constants.
    | .const nm =>
      match constTy? D nm with
      | some τ => some (τ, Γ, D)
      | none => claimTy c e |>.map (fun τ => (τ, Γ, D))
    | .cpath none nm =>
      match constTy? D nm with
      | some τ => some (τ, Γ, D)
      | none => claimTy c e |>.map (fun τ => (τ, Γ, D))
    | .cpath (some base) nm =>
      match chk c n D Γ base top ctx with
      | some (.clsOf cname, Γ₁, D₁) =>
        match scopedConstTy? D₁ cname nm with
        | some τ => some (τ, Γ₁, D₁)
        | none =>
          match claimTy c e with
          | some τ => some (τ, Γ₁, D₁)
          | none => none
      | _ => none
    -- **A constant *write* is checked and its type is not installed.** `Decls.consts`
    -- is a field of the table the certificate names, so a program that assigns a
    -- constant and then reads it wants the row in `deltaRows`, where it is a visible
    -- assumption — not silently threaded, which would be a table the residue does
    -- not mention. This is §9.7(b)'s `Assn.const` rung seen from the checker's side.
    | .casgn _ rhs =>
      match chk c n D Γ rhs top ctx with
      | some (τ, Γ₁, D₁) => some (τ, Γ₁, D₁)
      | none => none
    | .cpathAsgn base _ rhs =>
      match chkOpt c n D Γ base top ctx with
      | some (_, Γ₁, D₁) =>
        match chk c n D₁ Γ₁ rhs top ctx with
        | some (τ, Γ₂, D₂) => some (τ, Γ₂, D₂)
        | none => none
      | none => none
    -- ## Sends. One arm for all of them (`infer` has five), and the split it makes
    -- is on what is *present* — receiver, arguments, block — rather than on the
    -- shapes one pass happened to admit.
    | .send recvO mname args blkO =>
      match chkRecv c n D Γ recvO top ctx with
      | none => none
      | some (τr, Γ₁, D₁) =>
        match blkO with
        -- ### Block-less: the arguments, then the signature.
        | none =>
          match chkArgs c n top ctx D₁ Γ₁ args with
          | none => none
          | some (τs, Γ₂, D₂) =>
            match sigOf D₂ τr mname with
            | some (ps, τret) =>
              if subTys τs ps then some (τret, Γ₂, D₂)
              -- **C6/D2a.** The arity or a parameter did not match at the declared
              -- signature; a certificate may state the *instantiation* this site
              -- uses, and then the check is against that. Monomorphization, finite
              -- because call sites are finite.
              else if subTys τs (claimTys c e) then
                match claimTy c e with
                | some τ => some (τ, Γ₂, D₂)
                | none => none
              else none
            | none =>
              match claimTy c e with
              | some τ => if subTys τs (claimTys c e) then some (τ, Γ₂, D₂) else none
              | none => none
        -- ### A literal block. The two arms `infer` has, plus `lambda`, plus a
        -- claimed fallback for every other block-taking row.
        | some (.block ps ls body) =>
          match args with
          | [] =>
            match recvO with
            | some _ =>
              match blockSend? D₁ τr mname ps ls with
              | some (x, σp, βret, τret) =>
                match chk c n D₁ ((x, σp) :: anyEnv Γ₁) body false (blockCtx ctx) with
                | some (τb, Γb', D₂) =>
                  if subTy τb βret && D₂ == D₁ &&
                      subEnvB ((x, σp) :: anyEnv Γ₁) Γb' && ctx.inBlock == false then
                    some (τret, Γ₁, D₁)
                  else none
                | none => none
              | none => chkBlockClaim c n top ctx e D₁ Γ₁ [] ps ls body
            -- An implicit-self `lambda { … }` is the one block send with no
            -- receiver the fragment admits, and its answer is `.any`: a `Proc` has
            -- no row in any table, so nothing can be done with the value, which is
            -- exactly what the type says.
            | none =>
              if mname == "lambda" then some (.any, Γ, D)
              else chkBlockClaim c n top ctx e D Γ [] ps ls body
          | _ =>
            match chkArgs c n top ctx D₁ Γ₁ args with
            | none => none
            | some (τs, Γ₂, D₂) =>
              match blockSendA? D₂ τr mname ps ls with
              | some (x, σp, βret, dps, τret) =>
                match chk c n D₂ ((x, σp) :: anyEnv Γ₂) body false (blockCtx ctx)
                    with
                | some (τb, Γb', D₃) =>
                  if subTys τs dps && subTy τb βret && D₃ == D₂ && D₂ == D₁ && D₁ == D &&
                      subEnvB ((x, σp) :: anyEnv Γ₂) Γb' && ctx.inBlock == false then
                    some (τret, Γ₂, D₂)
                  else none
                | none => none
              | none => chkBlockClaim c n top ctx e D₂ Γ₂ τs ps ls body
        -- ### A block-pass `&e`. The operand is evaluated (or is the enclosing
        -- method's own block, anonymously forwarded); the row is claimed, because a
        -- `&:sym` is a `Symbol#to_proc` whose arity no signature records.
        | some (.blockpass bo) =>
          match chkArgs c n top ctx D₁ Γ₁ args with
          | none => none
          | some (τs, Γ₂, D₂) =>
            match chkOpt c n D₂ Γ₂ bo top ctx with
            | none => none
            | some (_, Γ₃, D₃) =>
              match claimTy c e with
              | some τ => if subTys τs (claimTys c e) then some (τ, Γ₃, D₃) else none
              | none =>
                match sigOf D₃ τr mname with
                | some (ps, τret) => if subTys τs ps then some (τret, Γ₃, D₃) else none
                | none => none
      -- A `blk` child that is neither a `block` nor a `blockpass` is not something
      -- the decoder emits. Refused by name rather than by a catch-all, so that a
      -- decoder change shows up here as a gap.
        | some _ => none
    -- A bare identifier that is not a local: an implicit-self, zero-argument,
    -- block-less send, and the shortest dispatch in the grammar.
    | .vcall mname =>
      match ctx.selfCls with
      | some cc =>
        match sigOf D (.cls cc) mname with
        | some ([], τret) => some (τret, Γ, D)
        | _ =>
          match claimTy c e with
          | some τ => some (τ, Γ, D)
          | none => none
      | none => none
    -- ## Argument-position markers. Each occurs only as a send's argument or an
    -- array element, and each has an arm here so that a certificate can address it
    -- — which is the whole of V10.
    | .kwargs entries =>
      match chkKwEntries c n top ctx D Γ entries with
      | some (Γ', D') => some (.cls "Hash", Γ', D')
      | none => none
    -- `...` forwards the enclosing `(...)`-method's captured arguments. There is no
    -- type for a forwarded argument *list*, so the marker answers `.any` and the
    -- callee's signature is what refuses it — which is the honest failure: nothing
    -- can be matched against a parameter by a value whose type is `.any`.
    | .fwd => some (.any, Γ, D)
    | .splat eo =>
      match eo with
      | none => some (.cls "Array", Γ, D)
      | some o =>
        match chk c n D Γ o top ctx with
        | some (.cls "Array", Γ₁, D₁) => some (.cls "Array", Γ₁, D₁)
        | some (.arrayOf τ, Γ₁, D₁) => some (.arrayOf τ, Γ₁, D₁)
        | _ => none
    -- A `block` node outside a send's `blk` position is not a value the machine
    -- ever evaluates; the send arms above consume it in place.
    | .block _ _ _ => none
    | .blockpass _ => none
    -- `yield` invokes the enclosing method's block. Its result type is the block's
    -- return type, which no `Decls` field records — so it is claimed, and the
    -- arguments are checked against the claimed parameter list.
    | .yield' args =>
      match chkArgs c n top ctx D Γ args with
      | some (τs, Γ', D') =>
        match claimTy c e with
        | some τ => if subTys τs (claimTys c e) then some (τ, Γ', D') else none
        | none => none
      | none => none
    -- ## Control flow.
    --
    -- The `if` join, and the arm where §4 D1's bet is actually placed. The
    -- deterministic answer is `joinTy`, which is *not* a least upper bound — it
    -- answers the four cases the fragment produces and refuses the rest. Where it
    -- refuses, a claimed type and environment are the stackmap entry, and what
    -- `chk` checks is that **each branch is below the claim** and each branch's
    -- environment contains the claimed one. That is exactly Rose's lightweight
    -- bytecode verification, and it is the milestone C5 asked for.
    | .if' cond t els =>
      match chk c n D Γ cond top ctx with
      | none => none
      | some (_, Γ₁, D₁) =>
        match els with
        | some el =>
          match chk c n D₁ Γ₁ t top ctx, chk c n D₁ Γ₁ el top ctx with
          | some (τt, Γt, Dt), some (τe, Γe, De) =>
            if subEnvB Γ₁ Γt && subEnvB Γ₁ Γe && Dt == De then
              match joinTy τt τe with
              | some τj => some (τj, Γ₁, Dt)
              | none =>
                match claimTy c e with
                | some τj =>
                  if subTy τt τj && subTy τe τj then
                    some (τj, claimEnv c e Γ₁, Dt)
                  else none
                | none => none
            else none
          | _, _ => none
        | none =>
          match chk c n D₁ Γ₁ t top ctx with
          | some (τt, Γt, Dt) =>
            if subEnvB Γ₁ Γt && Dt == D₁ then
              match joinTy τt .nilT with
              | some τj => some (τj, Γ₁, D₁)
              | none =>
                match claimTy c e with
                | some τj =>
                  if subTy τt τj && subTy .nilT τj then some (τj, claimEnv c e Γ₁, D₁)
                  else none
                | none => none
            else none
          | none => none
    -- A `while`'s condition and body must both leave the environment and the table
    -- where they found them — the loop-stability condition, and it is *equality*
    -- rather than containment because the loop's back edge re-enters at the entry
    -- environment. Where the body genuinely binds, the claimed environment is the
    -- loop head's stackmap and stability is checked against *that*.
    | .while' cond body =>
      let Γl := claimEnv c e Γ
      let ctxl := { ctx with inLoop := some Γl }
      match chk c n D Γl cond top ctxl with
      | some (_, Γ₁, D₁) =>
        if Γ₁ == Γl && D₁ == D then
          match chk c n D Γl body top ctxl with
          | some (_, Γ₂, D₂) => if Γ₂ == Γl && D₂ == D then some (.nilT, Γ, D) else none
          | none => none
        else none
      | none => none
    -- `begin body end while cond` — the body runs once, then the loop. Same
    -- stability condition, checked in the other order.
    | .dowhile body cond =>
      let Γl := claimEnv c e Γ
      let ctxl := { ctx with inLoop := some Γl }
      match chk c n D Γl body top ctxl with
      | some (_, Γ₁, D₁) =>
        if Γ₁ == Γl && D₁ == D then
          match chk c n D Γl cond top ctxl with
          | some (_, Γ₂, D₂) => if Γ₂ == Γl && D₂ == D then some (.nilT, Γ, D) else none
          | none => none
        else none
      | none => none
    -- `for tgts in coll; body; end`. The targets bind in the **enclosing** scope
    -- (no block frame; the loop variable leaks), which is why the answer's
    -- environment is the extended one and not `Γ`. An `arrayOf` collection gives
    -- the element type outright; anything else binds at `.any` or at the claim.
    -- Ruby's `for` evaluates to the collection.
    | .for' tgts coll body =>
      match chk c n D Γ coll top ctx with
      | none => none
      | some (τc, Γ₁, D₁) =>
        let τe := match τc with
          | .arrayOf τ => τ
          | _ => (claimTy c e).getD .any
        let Γb := bindTargets tgts τe Γ₁
        match chk c n D₁ Γb body top { ctx with inLoop := some Γb } with
        | some (_, Γ₂, D₂) => if Γ₂ == Γb && D₂ == D₁ then some (τc, Γb, D₁) else none
        | none => none
    -- ## Jumps. Each is sound only where its target exists, which is what the
    -- `FrameCtx` channels record.
    | .ret eo =>
      match ctx.ret with
      | some σ =>
        match eo with
        | some e' =>
          match chk c n D Γ e' top ctx with
          | some (τ, Γ₁, D₁) => if subTy τ σ then some (.nilT, Γ₁, D₁) else none
          | none => none
        | none => if subTy .nilT σ then some (.nilT, Γ, D) else none
      | none => none
    -- A `next` restarts the loop **in the same frame**, so the loop's entry
    -- environment has to be reconciled with the one the jump fires in — which is
    -- the one thing `next` costs that `return` does not.
    | .nxt eo =>
      if top then none
      else
        match ctx.inLoop with
        | some Γl =>
          match eo with
          | none => if subEnvB Γl Γ then some (.nilT, Γ, D) else none
          | some e' =>
            match chk c n D Γ e' top ctx with
            | some (_, Γ₁, D₁) =>
              if subEnvB Γl Γ₁ && D₁ == D then some (.nilT, Γ₁, D₁) else none
            | none => none
        | none => none
    -- `break` leaves the loop with a value, so unlike `next` it owes nothing about
    -- the loop's entry environment — the loop is over. What it owes is the *loop's*
    -- type, which is `nil` for a `while`; a `break` with a value in a `while` is
    -- therefore refused unless the claim says the loop's type.
    | .brk eo =>
      if top then none
      else
        match ctx.inLoop with
        | some _ =>
          match eo with
          | none => some (.nilT, Γ, D)
          | some e' =>
            match chk c n D Γ e' top ctx with
            | some (τ, Γ₁, D₁) =>
              match claimTy c e with
              | some σ => if subTy τ σ then some (.nilT, Γ₁, D₁) else none
              | none => none
            | none => none
        | none => none
    -- `retry` and `redo` transfer control backwards with no value. `retry` needs a
    -- `rescue` to restart and `redo` a loop iteration; neither is in `FrameCtx`'s
    -- channels, so both are claimed — a certificate that mentions the node is
    -- asserting the target exists, and `Machine`'s own `unwind` is what would
    -- refuse it at runtime.
    | .retry' =>
      match claimTy c e with
      | some _ => some (.nilT, Γ, D)
      | none => none
    | .redo' =>
      match ctx.inLoop with
      | some _ => some (.nilT, Γ, D)
      | none => none
    -- ## Definition forms.
    --
    -- A `def` evaluates to a Symbol (the method name) and *installs a row*, and the
    -- installation is the part that is guarded rather than derived: the row comes
    -- into force for the rest of the program, so every one of the five conditions
    -- below is a condition on the table the invariant will carry.
    | .def' name ps body =>
      match c.claimAt e with
      -- **The deterministic arm, and it is `infer`'s to the character** — the three
      -- hard refusals, the table-stability check, and the eight-clause promotion
      -- guard. Spelled out rather than factored with the claimed arm below, because
      -- `chk_infer`'s `def` case is a `simp` between *these two* expressions and a
      -- factoring would put a definition between them.
      | none =>
        if ps.isEmpty && declaresName D name == false && name != "method_added" && name != "define_method" then
          match chk c n D [] body false
              { ctx with selfCls := some ctx.cls, ret := none, meth := some name, inModuleBody := false,
                         params := some [], inClassBody := false, inLoop := none, inBlock := false }
              with
          | some (τb, _, Db) =>
            if Db == D then
              if top == false && name != "initialize" &&
                  reopenableClasses.contains ctx.cls &&
                  groundClassNames.contains ctx.cls == false && defFreeF n body &&
                  ctx.ret.isNone && ctx.inLoop.isNone && ctx.inBlock == false then
                some (.sym, Γ, addRow D ctx.cls name { params := [], ret := τb })
              else some (.sym, Γ, D)
            else none
          | none => none
        else none
      -- **The claimed arm: a `def` that takes parameters.** This is the population
      -- `infer` refuses outright (`params.isEmpty` is its first guard) and the one
      -- `slice-verdict.md`'s `open_params` column counts — 7 of the slice's 17
      -- accepts, which `bodyOk` *"cannot claim by construction"* (§9.6). The
      -- certificate supplies the declared parameter types and the declared return;
      -- `chk` binds the parameters and checks the body below the return.
      --
      -- No row is threaded. A parameterized `def`'s row is not witnessed at
      -- `Machine.init`'s heap any more than a nullary one is (V2), and the promotion
      -- `infer` performs for the nullary case is F1b.10's, which the invariant pays
      -- for with `UserEntryOk`. So this arm *checks the body* and leaves the table
      -- alone: the row, if the program needs one, is a `deltaRows` claim and visible
      -- in the residue.
      | some cl =>
        let τs := cl.tys.getD []
        if τs.length != ps.length then none
        else
          match chk c n D (bindParams n ps τs []) body false
              { ctx with selfCls := some ctx.cls, ret := some cl.ty, meth := some name,
                         params := some τs, inClassBody := false, inLoop := none, inBlock := false }
              with
          | some (τb, _, Db) =>
            if Db == D && subTy τb cl.ty then some (.sym, Γ, D) else none
          | none => none
    -- `def self.name` / `def obj.name` — a *singleton* method, so the row it
    -- installs is keyed on the class **object** (`tyClassNames (.clsOf n)` prefixes
    -- the name) and not on instances. The receiver is evaluated, the body is
    -- checked, and no row is threaded: a singleton row is a `deltaRows` claim,
    -- because `.clsOf`'s key is the one L264 measured as unreadable.
    | .defs recv name ps body =>
      match chk c n D Γ recv top ctx with
      | none => none
      | some (_, Γ₁, D₁) =>
        let τs := claimTys c e
        let Γb := bindParams n ps τs []
        match chk c n D₁ Γb body false
            { ctx with selfCls := none, ret := claimTy c e, meth := some name,
                       params := some τs, inClassBody := false, inLoop := none, inBlock := false } with
        | some (_, _, Db) => if Db == D₁ then some (.sym, Γ₁, D₁) else none
        | none => none
    -- `class C … end` reopens a constant looked up in the *current definee's* own
    -- table, and the only definee an invariant can describe is `Object` — hence the
    -- toplevel-position guard. The body's own table extension is threaded out,
    -- which is how a `def` inside the class becomes available afterwards.
    | .class' name sup body =>
      match sup with
      | none =>
        if top && reopenableClasses.contains name then
          match chk c n D [] body false { cls := name } with
          | some (τ, _, Db) => some (τ, Γ, Db)
          | none => none
        else none
      -- A superclass expression is evaluated, and then the reopen is *not* a reopen
      -- — it is a definition, whose ancestor chain the boot heap does not have. So
      -- the body is checked and the extension is **dropped**: rows on a class the
      -- program defines are `deltaRows`/C9 territory (V2).
      | some s =>
        match chk c n D Γ s top ctx with
        | none => none
        | some (_, Γ₁, D₁) =>
          match chk c n D₁ [] body false { cls := name } with
          | some (τ, _, _) => some (τ, Γ₁, D₁)
          | none => none
    | .module' name body =>
      match chk c n D [] body false { cls := name } with
      | some (τ, _, _) => some (τ, Γ, D)
      | none => none
    | .scopedClass base name body =>
      match chkOpt c n D Γ base top ctx with
      | none => none
      | some (_, Γ₁, D₁) =>
        match chk c n D₁ [] body false { cls := name } with
        | some (τ, _, _) => some (τ, Γ₁, D₁)
        | none => none
    | .scopedModule base name body =>
      match chkOpt c n D Γ base top ctx with
      | none => none
      | some (_, Γ₁, D₁) =>
        match chk c n D₁ [] body false { cls := name } with
        | some (τ, _, _) => some (τ, Γ₁, D₁)
        | none => none
    -- `class << obj` — the eigenclass body. The definee is the singleton, which has
    -- no name in the type language, so the body is checked at the claimed class name
    -- and its extension dropped for `.defs`' reason.
    | .sclass obj body =>
      match chk c n D Γ obj top ctx with
      | none => none
      | some (τo, Γ₁, D₁) =>
        let nm := match τo with
          | .clsOf n => n
          | _ => ctx.cls
        match chk c n D₁ [] body false { cls := nm } with
        | some (τ, _, _) => some (τ, Γ₁, D₁)
        | none => none
    -- ## `begin`/`rescue`/`else`/`ensure` — the L231/L233 join wall, and D1's second
    -- test case.
    --
    -- The region has as many exits as it has handlers plus one, and they leave
    -- *different* environments: the body may have assigned locals no handler sees.
    -- So the type of the whole region is stated at the entry environment (the one
    -- **every** path guarantees, which is `SubEnv`'s direction), and the type is the
    -- join of every exit — deterministically where `joinTy` folds, at the claim
    -- otherwise.
    | .begin' body rescues els ens =>
      match chk c n D Γ body top ctx with
      | none => none
      | some (τb, _, D₁) =>
        if D₁ != D then none
        else
          match chkRescues c n top ctx D Γ rescues with
          | none => none
          | some τr =>
            match (match els with
                   | none => some (τb, D)
                   | some el =>
                     match chk c n D Γ el top ctx with
                     | some (τl, _, Dl) => if Dl == D then some (τl, D) else none
                     | none => none) with
            | none => none
            | some (τe, _) =>
              match (match ens with
                     | none => some Ty.nilT
                     | some en =>
                       match chk c n D Γ en top ctx with
                       | some (_, _, Dn) => if Dn == D then some Ty.nilT else none
                       | none => none) with
              | none => none
              | some _ =>
                -- The exits: the body's (or the `else`'s, which replaces it) and
                -- every handler's.
                match joinAll (τe :: τr) with
                | some τj => some (τj, Γ, D)
                | none =>
                  match claimTy c e with
                  | some τj =>
                    if allBelow (τe :: τr) τj then some (τj, claimEnv c e Γ, D) else none
                  | none => none
    -- ## `super` and `zsuper`. The target is *this method's name*, looked up after
    -- the definee — so the rule needs `ctx.meth`, and bare `super` needs
    -- `ctx.params` as well, because it forwards the parameter *values* and their
    -- types are the declared ones.
    | .super' args blkO =>
      match ctx.meth with
      | none => none
      | some mn =>
        if mn == "" then none
        else
          match chkArgs c n top ctx D Γ args with
          | none => none
          | some (τs, Γ₁, D₁) =>
            match blkO with
            | none =>
              match superDecl? D₁ ctx.cls mn with
              | some d => if subTys τs d.params then some (d.ret, Γ₁, D₁) else none
              | none => none
            -- With a block the row is `blk`-bearing, which `sigOf` refuses by
            -- design (L242), so the answer is claimed.
            | some _ =>
              match claimTy c e with
              | some τ => some (τ, Γ₁, D₁)
              | none => none
    | .zsuper blkO =>
      match ctx.meth, ctx.params with
      | some mn, some ps =>
        if mn == "" then none
        else
          match blkO with
          | none =>
            match superDecl? D ctx.cls mn with
            | some d => if subTys ps d.params then some (d.ret, Γ, D) else none
            | none => none
          | some _ =>
            match claimTy c e with
            | some τ => some (τ, Γ, D)
            | none => none
      | _, _ => none
    -- ## The table-mutating statements. Both *remove* or *rebind* a name, so both
    -- invalidate a row the certificate may have claimed — and neither can be checked
    -- against a table that has no notion of removal. Refused unless the certificate
    -- claims the node, which is a reader-visible assertion that no claimed row is
    -- disturbed.
    | .undef _ =>
      match claimTy c e with
      | some _ => some (.nilT, Γ, D)
      | none => none
    | .alias' _ old =>
      match claimTy c e with
      | some _ => some (.nilT, Γ, D)
      | none =>
        -- With no claim, an alias is admissible exactly when the *old* name has no
        -- row in force: then no signature can be invalidated by the rebinding.
        if declaresName D old then none else some (.nilT, Γ, D)
    -- `defined?(e)` answers a String naming what `e` is, or nil — and the operand is
    -- **not evaluated**, except a send's receiver and a cpath's base. So the arm
    -- checks nothing about the operand and the answer is exact.
    | .defined _ => some (.nilable (.cls "String"), Γ, D)
    -- ## Composites.
    | .array es =>
      match chkElems c n top ctx D Γ es with
      | some (_, Γ', D') => some (.cls "Array", Γ', D')
      | none => none
    | .hash pairs =>
      match chkPairs c n top ctx D Γ pairs with
      | some (Γ', D') => some (.cls "Hash", Γ', D')
      | none => none
    | .seq es => chkSeq c n top ctx D Γ es

end

end RubyCore.Cert
