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

/-! ## 1. `Rec` — retired at V19

The list helpers used to take the recursive call as a **parameter** (`Rec`), which
kept them structural without a `mutual` block. That design cost exactly one thing,
and it turned out to be the expensive one: Lean could not derive `chk.induct`.

> `Cannot derive functional induction principle … failed to transform matcher … the
> argument has type (fun a => ∀ …) of sort Prop but is expected to have type Rec of
> sort Type`

A recursive call passed as a higher-order argument is what the induction-principle
generator cannot see through. And `chk.induct` is not a convenience:
`Proof/Static/Mono.lean`'s twenty structural laws are every one of them
`induction … using infer.induct with | motive2 … | motive5 …`, so without the
analogous principle each law is a hand-rolled fuel induction fighting `split` — which
is what V17's cost estimate was measuring, and it was measuring the wrong design.

The replacement is a `mutual` block in `Cert/Check.lean` in which **every** call
decreases the fuel, a helper's call into its own tail included. That is still
structural recursion on a `Nat`, so the kernel still reduces it (V9 intact, the
`decide`s still pass), and Lean derives `chk.induct` with one motive per function.

The price: fuel now bounds *node count* rather than depth, so `Cert.fuel`'s default is
larger. It still fails in the safe direction.

What stays here is what is *not* mutually recursive with `chk`: `defFreeF`, the
binding forms, and the joins.
-/

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
    | .hash prs => prs.all (fun p => defFreeF n p.1 && defFreeF n p.2)
    | .casgn _ rhs => defFreeF n rhs
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

end RubyCore.Cert
