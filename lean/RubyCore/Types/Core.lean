import RubyCore.Syntax

/-!
# P0 of the static-soundness POC — the type language and the checker

`docs/semantics/static-soundness-poc.md` §8. This is deliberately the smallest
type layer that exercises the whole architecture: three ground types, no
subtyping, no user classes, no `send`. Its purpose is not coverage — it is to
measure the cost of typing the machine's **continuation stack** before P1 fixes
a larger scope.

The checker is an **executable inference function**, and the typing judgment is
*defined by it* (`infer Γ e = some (τ, Γ')`). That is the certifying-checker
shape of the POC doc §2: no separate `Prop` to keep in sync, and no completeness
proof owed — `none` simply means `unknown`.

Inference is **flow-sensitive** in the environment (Ruby locals are assigned,
not declared), so every judgment threads an input and an output environment.
-/

namespace RubyCore.Types

/-- The P0 type language. No subtyping: `Sub` is equality, so it is not yet a
    separate relation. Widening this is P1/P3. -/
inductive Ty where
  | int
  | bool
  | nilT
deriving DecidableEq, Repr, Inhabited

/-- Local-variable typing environment. Order is canonical (`envSet` replaces in
    place) so that environment *equality* is a usable check — the `if`-merge and
    the loop-stability condition both need it. -/
abbrev Env := List (String × Ty)

def envGet? (Γ : Env) (x : String) : Option Ty :=
  (Γ.find? (·.1 == x)).map (·.2)

def envSet : Env → String → Ty → Env
  | [], x, τ => [(x, τ)]
  | (y, σ) :: Γ, x, τ => if y == x then (x, τ) :: Γ else (y, σ) :: envSet Γ x τ

/-! ## The builtin signature table

`static-soundness-poc.md` §5. The prelude-booted heap carries Ruby's core
library, none of which is in any typed fragment, so `WellTyped` cannot quantify
over it — builtins are carried by a **declared** signature instead.

Every entry is a **proof obligation**, not an assumption we get to keep: for
each one, the model's own implementation must be shown to conform
(`Proof/StaticSoundness.lean` §…). That is the RBI-conformance obligation of
`typed-portion-safety.md` §6, and our setting is better off than Sorbet's here —
Sorbet trusts its RBIs with no runtime backstop, whereas the model *defines* the
builtin, so conformance is a lemma.

The table is keyed on the receiver's **static type**, which is enough at P0
where `Ty` and the dispatch class are in bijection. P1 needs class names.
-/

/-- Declared `(parameter types, return type)` of a builtin, or `none` for
    "not in the table", which the checker reads as `unknown`.

    Deliberately narrow: only entries whose conformance lemma is proved may
    appear. Notable absences and why —

    * `/` and `%` — `ZeroDivisionError`. Not a *type* error, so admitting them
      would not endanger `check_sound`, but their conformance lemma needs a
      side condition and they buy nothing at P0.
    * `**` — a negative exponent produces a Rational in Ruby, which the model
      does not have.
    * the `Float` cases of the same bids — `numBin` promotes `Int × Float` to
      `Float`, so `Integer#+` is only `int → int` because the *argument* type
      is pinned by the table. -/
def builtinSig : Ty → String → Option (List Ty × Ty)
  | .int, "+" => some ([.int], .int)
  | .int, "-" => some ([.int], .int)
  | .int, "*" => some ([.int], .int)
  | _, _ => none

mutual

/-- `infer Γ e = some (τ, Γ')` — `e` has type `τ` and leaves the environment
    `Γ'`. `none` is `unknown`: outside the P0 fragment, or ill-typed. -/
def infer (Γ : Env) (e : Expr) : Option (Ty × Env) :=
  match e with
  | .int _ => some (.int, Γ)
  | .tru => some (.bool, Γ)
  | .fls => some (.bool, Γ)
  | .nil => some (.nilT, Γ)
  | .var .lvar x => (envGet? Γ x).map (fun τ => (τ, Γ))
  | .vasgn .lvar x rhs =>
    match infer Γ rhs with
    | some (τ, Γ₁) => some (τ, envSet Γ₁ x τ)
    | none => none
  -- Binary send to a builtin, explicit receiver, no block. Every other send
  -- shape — implicit self, wrong arity, a block, `vcall` — is `unknown`, which
  -- is also what keeps `.self'` out of receiver position (see `KontOk.recvK`:
  -- `evalExpr` picks the `.selfRecv` site *syntactically* for a literal `self`).
  | .send (some recv) mname [arg] none =>
    match infer Γ recv with
    | some (τr, Γ₁) =>
      match builtinSig τr mname with
      | some ([τp], τret) =>
        match infer Γ₁ arg with
        | some (τa, Γ₂) => if τa = τp then some (τret, Γ₂) else none
        | none => none
      | _ => none
    | none => none
  | .seq es => inferSeq Γ es
  | .if' c t els =>
    match infer Γ c with
    | some (_, Γ₁) => inferIf Γ₁ t els
    | none => none
  | .while' c body =>
    -- The loop re-enters the condition with the environment the body leaves, so
    -- both must be *stable* at `Γ`. This is the P0 stand-in for a fixpoint.
    match infer Γ c with
    | some (_, Γ₁) =>
      if Γ₁ = Γ then
        match infer Γ body with
        | some (_, Γ₂) => if Γ₂ = Γ then some (.nilT, Γ) else none
        | none => none
      else none
    | none => none
  | _ => none
termination_by sizeOf e

/-- Statement sequence: thread the environment, take the last type. Mirrors
    `evalExpr`'s three-way split on `.seq` (`Interp.lean:2732`) exactly — in
    particular `[e]` steps straight to `e` with no `seqK` pushed. -/
def inferSeq (Γ : Env) (es : List Expr) : Option (Ty × Env) :=
  match es with
  | [] => some (.nilT, Γ)
  | [e] => infer Γ e
  | e :: rest =>
    match infer Γ e with
    | some (_, Γ₁) => inferSeq Γ₁ rest
    | none => none
termination_by sizeOf es

/-- The `if` join, factored out because `KontOk.ifK` must agree with it
    branch-for-branch. No union type in P0, so the two arms must agree on both
    the type and the environment; a missing `else` contributes `nil` and no
    environment change (`applyKont`'s fall-through, `Interp.lean:2096`). -/
def inferIf (Γ : Env) (t : Expr) (els : Option Expr) : Option (Ty × Env) :=
  match els with
  | some e =>
    match infer Γ t, infer Γ e with
    | some (τt, Γt), some (τe, Γe) =>
      if τt = τe ∧ Γt = Γe then some (τt, Γt) else none
    | _, _ => none
  | none =>
    match infer Γ t with
    | some (τt, Γt) => if τt = Ty.nilT ∧ Γt = Γ then some (.nilT, Γ) else none
    | none => none
termination_by sizeOf t + sizeOf els

end

/-- The POC verdict lattice (doc §2.2): two-valued. There is deliberately no
    `reject` — a rejection is a claim about our rules and needs its own guard
    and its own difftest direction. -/
inductive Verdict where
  | accept
  | unknown
deriving DecidableEq, Repr, Inhabited

/-- **The checker.** Total and executable; `accept` is what `check_sound`
    licenses. -/
def check (p : Expr) : Verdict :=
  match infer [] p with
  | some _ => .accept
  | none => .unknown

end RubyCore.Types
