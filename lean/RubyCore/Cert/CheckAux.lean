import RubyCore.Cert.Format

/-!
# `chk`'s auxiliaries — the list combinators, the binding forms, the joins

Split out of `Cert/Check.lean` under §7 norm 3 (*files under 1,000 lines, one concern
per file*): `chk` itself is one concern and the machinery it defers to is another.
Everything here obeys the same discipline as `chk` and for the same reason (V9) —
**nothing recurses on syntax except through fuel**, because the checked path has to
reduce in the kernel.

The list helpers take the recursive call as a **parameter** rather than sitting in a
`mutual` block with `chk`: a mutual block at the same fuel value is well-founded
recursion again, which is the whole thing this initiative exists to avoid. That is
also why they are usable as standalone lemma subjects — `Proof/Cert/Mono.lean` §1
states one law per helper, which is the shape that replaces `infer.induct`'s
`motive3`…`motive5`.
-/

namespace RubyCore.Cert

open RubyCore.Types

/-! ## 1. The recursive-call type, and the list helpers

`chk` recurses on fuel and the list helpers recurse on their list, so the two never
have to decrease together — which is what keeps *both* structural. The helpers take
the recursive call as a **parameter** rather than sitting in a `mutual` block with
`chk`: a mutual block at the same fuel value is well-founded recursion again, and
well-founded recursion is the whole thing this file exists to avoid (V9).

The `Path` argument of each helper is the *parent's* path plus the index of the
first element, so a helper extends what its caller built. -/

/-- The type of `chk` at a fixed certificate and fuel — the callback the list
    helpers take. -/
abbrev Rec := Decls → Env → Expr → Bool → FrameCtx → Option (Ty × Env × Decls)

/-- A statement sequence: thread the environment and the table, take the last type.
    An empty sequence is `nil`, and `[e]` is `e` — the three-way split `evalExpr`
    makes on `.seq`. -/
def chkSeq (f : Rec) (top : Bool) (ctx : FrameCtx) :
    Decls → Env → List Expr → Option (Ty × Env × Decls)
  | D, Γ, [] => some (.nilT, Γ, D)
  | D, Γ, [e] => f D Γ e top ctx
  | D, Γ, e :: rest =>
    match f D Γ e top ctx with
    | some (_, Γ₁, D₁) => chkSeq f top ctx D₁ Γ₁ rest
    | none => none

/-- An argument list: the same threading, but the *types* are kept in order, because
    that is what a signature's parameter list is matched against. -/
def chkArgs (f : Rec) (top : Bool) (ctx : FrameCtx) :
    Decls → Env → List Expr → Option (List Ty × Env × Decls)
  | D, Γ, [] => some ([], Γ, D)
  | D, Γ, e :: rest =>
    match f D Γ e top ctx with
    | some (τ, Γ₁, D₁) =>
      match chkArgs f top ctx D₁ Γ₁ rest with
      | some (τs, Γ₂, D₂) => some (τ :: τs, Γ₂, D₂)
      | none => none
    | none => none

/-- The elements of an array literal. Element types are erased (`.array` answers
    `.cls "Array"`), and a `.splat` element's operand must be exactly `Array` —
    which is what makes the step total, since `spreadA` errors on any other
    payload. -/
def chkElems (f : Rec) (top : Bool) (ctx : FrameCtx) :
    Decls → Env → List Expr → Option (Ty × Env × Decls)
  | D, Γ, [] => some (.nilT, Γ, D)
  | D, Γ, e :: rest =>
    match e with
    | .splat (some o) =>
      match f D Γ o top ctx with
      | some (.cls "Array", Γ₁, D₁) => chkElems f top ctx D₁ Γ₁ rest
      | _ => none
    | ee =>
      match f D Γ ee top ctx with
      | some (_, Γ₁, D₁) => chkElems f top ctx D₁ Γ₁ rest
      | none => none

/-- The pairs of a hash literal — key then value, left to right, threading both.
    A `**h` double-splat is a `.splat` in the key position with the value unused,
    which is how the decoder emits it. -/
def chkPairs (f : Rec) (top : Bool) (ctx : FrameCtx) :
    Decls → Env → List (Expr × Expr) → Option (Env × Decls)
  | D, Γ, [] => some (Γ, D)
  | D, Γ, (k, v) :: rest =>
    match f D Γ k top ctx with
    | some (_, Γ₁, D₁) =>
      match f D₁ Γ₁ v top ctx with
      | some (_, Γ₂, D₂) => chkPairs f top ctx D₂ Γ₂ rest
      | none => none
    | none => none

/-- The entries of a brace-less keyword-argument marker. Each entry's *value* is
    evaluated; a `.dyn` entry's key is too. -/
def chkKwEntries (f : Rec) (top : Bool) (ctx : FrameCtx) :
    Decls → Env → List KwEntry → Option (Env × Decls)
  | D, Γ, [] => some (Γ, D)
  | D, Γ, e :: rest =>
    match e with
    | .pair _ v =>
      match f D Γ v top ctx with
      | some (_, Γ₁, D₁) => chkKwEntries f top ctx D₁ Γ₁ rest
      | none => none
    | .splat v =>
      match f D Γ v top ctx with
      | some (_, Γ₁, D₁) => chkKwEntries f top ctx D₁ Γ₁ rest
      | none => none
    | .dyn k v =>
      match f D Γ k top ctx with
      | some (_, Γ₁, D₁) =>
        match f D₁ Γ₁ v top ctx with
        | some (_, Γ₂, D₂) => chkKwEntries f top ctx D₂ Γ₂ rest
        | none => none
      | none => none

/-! ## 1a. `defFree`, re-spelled on fuel (V13)

`Types/Core.lean` has this predicate already and **this file may not import it**: it
lives in the module that defines `infer`, and the import discipline V12 establishes is
the whole point of the rewrite. It is also well-founded-recursive, so it would not
reduce in the kernel even if it were reachable.

So it is re-spelled here, arm for arm, on fuel. This is the *one* place the
initiative keeps a private copy of something the standing tree has, and norm 7 is
explicit that a private copy is normally forbidden — so the copy is paid for the way
a copy has to be: `defFreeF_sound` (`Proof/Cert/Check.lean`) proves
`defFreeF n e = true → defFree e = true`, which is what the bridge to `infer`'s
`def` arm consumes. The two cannot drift silently, because the drift is a broken
proof.

Fuel exhaustion answers `false`, i.e. *refuses* — the same direction every other
fuel bound in this file fails in. -/

/-- The list arm of `defFreeF`, with the recursive call as a parameter. -/
def defFreeFAll (g : Expr → Bool) : List Expr → Bool
  | [] => true
  | e :: rest => g e && defFreeFAll g rest

/-- No `def` and no `class` anywhere in the expression — `Types/Core.lean`'s
    `defFree`, on fuel. -/
def defFreeF : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, e =>
    match e with
    | .def' _ _ _ => false
    | .class' _ _ _ => false
    | .seq es => defFreeFAll (defFreeF n) es
    | .if' cnd t els =>
      defFreeF n cnd && defFreeF n t &&
        (match els with | some e' => defFreeF n e' | none => true)
    | .while' cnd b => defFreeF n cnd && defFreeF n b
    | .vasgn _ _ rhs => defFreeF n rhs
    | .send r _ args blk =>
      (match r with | some r' => defFreeF n r' | none => true) &&
        defFreeFAll (defFreeF n) args &&
        (match blk with | some b => defFreeF n b | none => true)
    | .block _ _ b => defFreeF n b
    | .array es => defFreeFAll (defFreeF n) es
    | .ret eo => match eo with | some e' => defFreeF n e' | none => true
    | .cpath base _ => match base with | some b => defFreeF n b | none => true
    | .super' args blk =>
      defFreeFAll (defFreeF n) args &&
        (match blk with | some b => defFreeF n b | none => true)
    | .splat eo => match eo with | some e' => defFreeF n e' | none => true
    | .nxt none => true
    | .zsuper blk => match blk with | some b => defFreeF n b | none => true
    | _ => true

/-! ## 2. Binding forms

Two helpers that are about *names*, not about types, and are shared by the four arms
that introduce bindings (`.def'`/`.defs` parameters, `.block` parameters,
`.for'` targets). -/

/-- Bind a parameter list at the declared types the certificate supplies, in order.
    A parameter kind with no declared type — a rest, a keyword-rest, a block capture,
    a forward — binds at `.any`, which is honest: nothing can be done with an
    `.any`-typed local, so a body that uses one does not check.

    A **destructuring** parameter binds its own sub-names at `.any` rather than
    distributing the declared type, because the type language has no tuple and
    `arrayOf`'s element type is not what a `(a, b)` pattern takes apart.

    **On fuel**, for `destr`'s sake and V9's reason: `.destr subs` recurses into a
    `List Param` *inside* the head element, which is a nested inductive, so Lean
    compiles the structural version by well-founded recursion and the kernel gets
    stuck on it. Measured — the first draft would not `decide` a parameterized
    `def`. Fuel exhaustion leaves the environment unextended, so the body's read of
    an unbound parameter refuses: the safe direction again. -/
def bindParams : Nat → List Param → List Ty → Env → Env
  | _, [], _, Γ => Γ
  | 0, _, _, Γ => Γ
  | n + 1, p :: ps, τs, Γ =>
    match p, τs with
    | .req x, τ :: τs' => bindParams n ps τs' (envSet Γ x τ)
    | .req x, [] => bindParams n ps [] (envSet Γ x .any)
    | .opt x _, τ :: τs' => bindParams n ps τs' (envSet Γ x τ)
    | .opt x _, [] => bindParams n ps [] (envSet Γ x .any)
    | .key x _, τ :: τs' => bindParams n ps τs' (envSet Γ x τ)
    | .key x _, [] => bindParams n ps [] (envSet Γ x .any)
    | .rest (some x), _ => bindParams n ps τs (envSet Γ x .any)
    | .rest none, _ => bindParams n ps τs Γ
    | .kwrest (some x), _ => bindParams n ps τs (envSet Γ x .any)
    | .kwrest none, _ => bindParams n ps τs Γ
    | .block (some x), _ => bindParams n ps τs (envSet Γ x .any)
    | .block none, _ => bindParams n ps τs Γ
    | .fwd, _ => bindParams n ps τs Γ
    | .destr subs, _ => bindParams n ps τs (bindParams n subs [] Γ)

/-- The names a `for` loop's targets bind — in the **enclosing** scope, because a
    `for` pushes no frame and the loop variable leaks [V]. At `.any`, for
    `bindParams`' reason: the collection's element type is not in the type language
    unless it is an `arrayOf`, and the `.for'` arm reads that case out separately. -/
def bindTargets : List (TargetKind × String) → Ty → Env → Env
  | [], _, Γ => Γ
  | (_, x) :: rest, τ, Γ => bindTargets rest τ (envSet Γ x τ)

/-! ## 3. The helpers `chk`'s arms defer to

Each is here rather than inline for the reason norm 3 gives: they are separate
concerns, and two of them are *joins*, which is the one place a checker is allowed
to be interesting. -/

/-- The fold of a list of exit types. `joinTy` is not a least upper bound, so the
    fold refuses where it refuses — which is exactly where the certificate's claim
    is asked for. -/
def joinAll : List Ty → Option Ty
  | [] => some .nilT
  | [τ] => some τ
  | τ :: rest =>
    match joinAll rest with
    | some σ => joinTy τ σ
    | none => none

/-- Is every exit type below the claimed join? The check a stackmap entry owes. -/
def allBelow : List Ty → Ty → Bool
  | [], _ => true
  | τ :: rest, σ => subTy τ σ && allBelow rest σ

/-- The handlers of a `begin` region: each is checked at the **entry** environment,
    because a handler may run after any prefix of the body and nothing the body bound
    is guaranteed. The exception-class list is checked as an ordinary expression list
    (each entry is a constant read); the target binds the exception, at the claimed
    type or at the first class named. -/
def chkRescues (c : Cert) (f : Rec) (top : Bool) (ctx : FrameCtx) :
    Decls → Env → List (List Expr × Option (TargetKind × String) × Expr) →
    Option (List Ty)
  | _, _, [] => some []
  | D, Γ, (excs, tgt, hbody) :: rest =>
    match chkArgs f top ctx D Γ excs with
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
        match f D Γh hbody top ctx with
        | none => none
        | some (τh, _, Dh) =>
          if Dh != D then none
          else
            match chkRescues c f top ctx D Γ rest with
            | some τrs => some (τh :: τrs)
            | none => none

/-- A block send whose row `blockSend?`/`blockSendA?` does not supply — the claimed
    arm. The block's body is still **checked**, at the claimed parameter type, so
    what the certificate supplies is the row and not the body's typing. -/
def chkBlockClaim (c : Cert) (f : Rec) (_top : Bool) (ctx : FrameCtx) (key : Expr)
    (D : Decls) (Γ : Env) (τs : List Ty) (ps : List Param) (ls : List String)
    (body : Expr) : Option (Ty × Env × Decls) :=
  let _ := ls
  let _ := τs
  match c.claimAt key with
  | none => none
  | some cl =>
    let τp := match cl.tys with
      | some (τ :: _) => τ
      | _ => .any
    let Γb := bindParams 64 ps [τp] (anyEnv Γ)
    match f D Γb body false (blockCtx ctx) with
    | some (_, _, D') => if D' == D && ctx.inBlock == false then some (cl.ty, Γ, D) else none
    | none => none

end RubyCore.Cert
