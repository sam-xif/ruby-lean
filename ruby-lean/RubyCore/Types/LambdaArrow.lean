import RubyCore.Types.SigRead

/-!
# A standalone checker for `T.proc`-typed lambdas

`docs/semantics/typed-lambdas-plan.md`. This is deliberately **not** a rule
added to `Types/Core.lean`'s `infer`: that function's `mutual` group is shared
with the whole P0 fragment, and `Proof/Static/Mono.lean`'s three `infer.induct`
sites address cases by their **positional** auto-generated name (`case113` and
friends) — the file's own note records that widening `infer`'s cases before
"cost a full renumbering of `Mono.lean` twice". Any new branch inside `infer`
shifts those names program-wide, several theorems deep, for a feature the rest
of the checker's fragment has no reason to know about.

So this is a **second, small, self-contained checker**, over the exact
fragment the plan's forcing example needs: a flat sequence of top-level,
**zero-argument** `def`s (each optionally preceded by a `sig { … }` declaring a
`T.proc.params(...).returns(...)` return type), followed by a driver
expression. Nothing elsewhere in the codebase depends on this function's
shape or its induction principle, so it is free to grow without the blast
radius `infer` has.

## Design, mapped from the plan's §0

* **The body check is bidirectional only in tail position.** `chkSeq`'s
  `[e]` arm is the only one that passes `expected` through; every earlier
  statement is checked with `none` (infer, not check). That is what makes
  "a lambda literal in tail/return position of a `def` whose declared return
  type is `.proc dom cod`" (L2) exact rather than "anywhere `ctx.ret` happens
  to be visible" — the shape a first attempt at this file took, and abandoned
  for being over-eager rather than for being unsound.
* **Pinning rides in `Γ` itself**, via `Types/Ty.lean`'s `pinKey`/`pinTy?`/
  `addPins` — a reserved-key shadow entry, not a side table. `.vasgn`'s arm
  below is the consumer.
* **No table threading.** Every `def` here is top-level and zero-argument, so
  the return-type table (`RetTable`) is closed once, up front, by `chkTop`;
  nothing inside a body can grow it. That is the simplification this smaller
  fragment buys over `infer`'s `Decls`, which has to thread because `class'`
  and (once params land) nested `def`s can.
-/

namespace RubyCore.Types.TL

/-- Zero-arg method name → declared return type, closed once for the whole
    program before any body is checked (`chkTop`). -/
abbrev RetTable := List (String × Ty)

def retOf? (R : RetTable) (name : String) : Option Ty :=
  (R.find? (·.1 == name)).map (·.2)

/-- A lambda literal's parameter names, only if every one is `.req` — the
    plan's L2 gate (no keyword/optional/splat/block param in `dom`). -/
def allReq? : List Param → Option (List String)
  | [] => some []
  | .req x :: rest => (allReq? rest).map (x :: ·)
  | _ :: _ => none

mutual

/-- **The checker.** `expected` is the bidirectional channel: `some τ` only at
    a position with a known expected type (a tail position under a declared
    return, `chkSeq`'s `[e]` arm), `none` everywhere else. -/
def chk (R : RetTable) (Γ : Env) (e : Expr) (expected : Option Ty) :
    Option (Ty × Env) :=
  match e with
  | .int _ => some (.int, Γ)
  | .str _ => some (.cls "String", Γ)
  | .sym _ => some (.sym, Γ)
  | .tru => some (.bool, Γ)
  | .fls => some (.bool, Γ)
  | .nil => some (.nilT, Γ)
  | .var .lvar x => (envGet? Γ x).map (fun τ => (τ, Γ))
  -- **The pin check** (plan §0 item 3): once a lambda has captured `x`
  -- (`addPins`, below), every later assignment to it must conform to the
  -- type it had at capture. `pinTy? Γ₁ x = none` on every name no lambda in
  -- this program has ever captured, which is the fallback that keeps this
  -- arm total.
  | .vasgn .lvar x rhs =>
    match chk R Γ rhs none with
    | some (τ, Γ₁) =>
      match pinTy? Γ₁ x with
      | some τpin => if subTy τ τpin then some (τ, envSet Γ₁ x τ) else none
      | none => some (τ, envSet Γ₁ x τ)
    | none => none
  | .seq es => chkSeq R Γ es expected
  -- **The lambda arrow rule** (L2). Fires only when `expected` names an
  -- arrow (`Ty.arrowOf`/`arrowParts?`, `Types/Ty.lean`'s L1 bridge — reused
  -- rather than a fresh `Ty.proc` arm, since it already exists, already has
  -- `subTy`/`tyClassNames` treating it as inert-on-the-checker-path, and
  -- already has no `valueTy?` arm). Gate unless every param is `.req`, the
  -- arity matches, and there are no block-locals; check the body at
  -- `(params zip dom) ++ Γ` — every enclosing local is offered as a capture,
  -- a sound over-approximation of the body's free variables (pinning a name
  -- the body never reads only rejects more programs, never fewer, so this
  -- needs no walk of `Expr` to get right); require the result below `cod`.
  -- A **failed** check here is `none`, not a fall-back to `.any` — the whole
  -- point of the mutation tests is that a violation at a *known* expected
  -- type is caught, not shrugged at. `expected = none` (no declared arrow in
  -- scope) is the one case that *does* fall back, to the plain-lambda answer
  -- every value of this shape must have *some* type at.
  | .send none "lambda" [] (some (.block ps ls body)) =>
    match expected.bind arrowParts? with
    | none => some (.any, Γ)
    | some (dom, cod) =>
      match allReq? ps with
      | none => none
      | some names =>
        if names.length == dom.length ∧ ls = [] then
          match chk R ((names.zip dom) ++ Γ) body (some cod) with
          | some (τb, _) => if subTy τb cod then some (arrowOf dom cod, addPins Γ) else none
          | none => none
        else none
  -- **The arrow's eliminator** (L4): `.call` on a receiver whose checked type
  -- is an arrow. Args must be below the declared parameters and match arity
  -- exactly (lambda arity semantics — the intro rule above mints arrows only
  -- for lambdas, never for lenient `proc`/`Proc.new`).
  | .send (some r) "call" args none =>
    match chk R Γ r none with
    | some (τr, Γ₁) =>
      match arrowParts? τr with
      | some (dom, cod) =>
        match chkArgs R Γ₁ args with
        | some (τs, Γ₂) => if τs.length == dom.length ∧ subTys τs dom then some (cod, Γ₂) else none
        | none => none
      | none => none
    | none => none
  -- A bare call to a declared zero-arg top-level method (`comparator_for`,
  -- `use_comparator`) — the "distant" half of "a declared return type rides
  -- through a local to a distant `.call`" starts here, one call before the
  -- arrow even exists.
  | .vcall name => (retOf? R name).map (fun τ => (τ, Γ))
  | _ => none
termination_by sizeOf e

def chkSeq (R : RetTable) (Γ : Env) (es : List Expr) (expected : Option Ty) :
    Option (Ty × Env) :=
  match es with
  | [] => some (.nilT, Γ)
  -- **Tail position**: the only place `expected` survives to, syntactically.
  | [e] => chk R Γ e expected
  -- **Copy-propagation for the bidirectional channel** (typed-lambdas L2):
  -- if the whole sequence's tail is a bare read of some name `x`, the
  -- sequence's expected type *is* the expected type for whichever statement
  -- assigns `x` — even when that assignment is not itself the sequence's
  -- last element, and even when other statements sit between it and the
  -- tail. This is what lets the plan's pin-mutation falsifier exist at all:
  -- a captured variable is reassigned *after* the lambda that captured it
  -- and *before* the method returns it, so the lambda that needs
  -- `expected` is never the sequence's syntactic last element. Matched as a
  -- direct top-level pattern on `es`, not jointly with `expected`/
  -- `es.getLast?` in a nested `match` — the latter was tried first and
  -- confused the equation compiler's decreasing-measure search (`e`, having
  -- been re-matched inside a tuple, stopped looking like a strict subterm
  -- of `e :: rest` to it).
  | (.vasgn .lvar x rhs) :: rest =>
    if expected.isSome ∧ es.getLast? == some (.var .lvar x) then
      match chk R Γ rhs expected with
      | some (τ, Γ₁) =>
        match pinTy? Γ₁ x with
        | some τpin => if subTy τ τpin then chkSeq R (envSet Γ₁ x τ) rest expected else none
        | none => chkSeq R (envSet Γ₁ x τ) rest expected
      | none => none
    else
      match chk R Γ (.vasgn .lvar x rhs) none with
      | some (_, Γ₁) => chkSeq R Γ₁ rest expected
      | none => none
  | e :: rest =>
    match chk R Γ e none with
    | some (_, Γ₁) => chkSeq R Γ₁ rest expected
    | none => none
termination_by sizeOf es

def chkArgs (R : RetTable) (Γ : Env) (es : List Expr) : Option (List Ty × Env) :=
  match es with
  | [] => some ([], Γ)
  | e :: rest =>
    match chk R Γ e none with
    | some (τ, Γ₁) =>
      match chkArgs R Γ₁ rest with
      | some (τs, Γ₂) => some (τ :: τs, Γ₂)
      | none => none
    | none => none
termination_by sizeOf es

end

/-- **The whole program**: a flat list of top-level statements. Each
    `sig { … }` immediately followed by a zero-arg `def` declares a row —
    checked against the sig's declared type when it reads as one (the
    creation-site check, L2), against the body's own inferred type otherwise
    (mirroring `Types/Core.lean`'s `.def'`, the existing discipline for a
    `def` with no readable sig). Any other statement (the driver) is checked
    and its type discarded — only the last one's answer is the program's.

    Structural recursion on the list, calling only non-`partial` functions
    (`chk`, `readSigChain`, `toTy`, `sigBody?`), so — unlike `SigRead.lean`'s
    `collectSigs`, which this deliberately does *not* call — its equations
    are usable inside a proof. -/
def chkTop : RetTable → List Expr → Option Ty
  | _, [] => some .nilT
  | R, [e] => (chk R [] e none).map Prod.fst
  -- **A `sig` immediately followed by a `def`** — the pair association is by
  -- adjacency (`SigRead.lean`'s `collectSigs` note, same reason). A readable
  -- `T.proc` return type is the *expected* type the body is checked against
  -- (L2); anything else falls through to the plain `def` arm below at the
  -- unread `sig`'s cost of one wasted statement (still `Some ()`-checked, via
  -- `chk`'s catch-all, not skipped).
  | R, e :: (.def' name [] body :: rest') =>
    match sigBody? e with
    | some sb =>
      let declTy? := (readSigChain sb).bind (·.ret) |>.bind toTy
      match chk R [] body declTy? with
      | some (τb, _) =>
        match declTy? with
        | some dt => if subTy τb dt then chkTop ((name, dt) :: R) rest' else none
        | none => chkTop ((name, τb) :: R) rest'
      | none => none
    | none =>
      match chk R [] e none with
      | some _ =>
        match chk R [] body none with
        | some (τb, _) => chkTop ((name, τb) :: R) rest'
        | none => none
      | none => none
  -- **A bare `def`** (no readable preceding `sig`, or no `sig` at all): the
  -- row is the body's own inferred type, `.def'`'s existing discipline.
  | R, .def' name [] body :: rest =>
    match chk R [] body none with
    | some (τb, _) => chkTop ((name, τb) :: R) rest
    | none => none
  -- **A driver statement**: checked when it is in this fragment at all,
  -- `R` carried forward unchanged either way. Out-of-fragment preamble
  -- (`require "sorbet-runtime"`, `extend T::Sig` — sends this checker has no
  -- rule for at all, never mind a wrong one) is skipped rather than rejected:
  -- this checker's whole reason to exist is the lambda/sig/`.call` mechanism,
  -- and gating the file on unrelated boilerplate would test nothing about it.
  -- The one statement this *cannot* silently pass is the last one — the
  -- `[e]` arm above has no such fallback, so the program's reported type is
  -- always a real verdict on real content.
  | R, _ :: rest => chkTop R rest

/-- The CLI/top-level entry point: `some τ` is acceptance at `τ`, `none` is
    "unknown" — the checker's `--check` verdict, transcribed. -/
def checkTL (p : Expr) : Option Ty :=
  match p with
  | .seq es => chkTop [] es
  | e => chkTop [] [e]

end RubyCore.Types.TL
