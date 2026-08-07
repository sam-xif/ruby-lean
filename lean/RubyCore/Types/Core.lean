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

/-! ## The refutation pass

`static-soundness-poc.md` §2.2 deferred a `reject` verdict; this supplies it, as
a **second pass independent of `infer`**. The separation is deliberate: `infer`'s
`none` conflates "outside the fragment" with "ill-typed", and threading a third
value through it would touch every `KontOk` constructor and every case of the
preservation proof for no gain. `check_sound` is about `accept` and is untouched
by anything here.

**What `reject` claims.** Only that *our rules refute the program* — not that it
will fail at runtime. `if false then 1 + nil else 0 end` is rejected and is
perfectly safe. That asymmetry is inherent (`typed-portion-safety.md` §8.1) and
is why the guard on `reject` is a difftest direction — `reject ⇒ srb rejects` —
rather than a Lean theorem. Verified for the cases below [V].

**Bias toward `unknown`.** Every source of doubt resolves to `unknown`:
a receiver or argument whose type is not *unconditional*, a method absent from
`builtinSig`, or any expression outside the fragment's spine.
-/

/-- The type of an expression when it is **unconditional** — literals, and sends
    whose operands are themselves unconditional. Deliberately takes no
    environment, so a local variable is always `none`: `q = 1; q + nil` is
    `unknown` here though `srb` rejects it [V]. That is incompleteness, which
    the ratchet is allowed to have; it is also the obvious next widening. -/
def defTy (e : Expr) : Option Ty :=
  match e with
  | .int _ => some .int
  | .tru => some .bool
  | .fls => some .bool
  | .nil => some .nilT
  | .send (some r) mname [a] none =>
    match defTy r with
    | some τr =>
      match builtinSig τr mname with
      | some ([τp], τret) =>
        match defTy a with
        | some τa => if τa = τp then some τret else none
        | none => none
      | _ => none
    | none => none
  | _ => none
termination_by sizeOf e

/-- Does the table *definitely* refute this call? Requires the receiver and the
    argument to have unconditional types **and** the method to be in the table.

    A method the table does not carry is `false`, not `true`: the table is
    narrow on purpose (`/` is absent but perfectly valid), so absence means "no
    opinion". `1.foo(2)` is therefore `unknown` here even though `srb` rejects it
    with 7003 [V] — again incompleteness, never unsoundness. -/
def tableRefutes (r : Expr) (mname : String) (a : Expr) : Bool :=
  match defTy r, defTy a with
  | some τr, some τa =>
    match builtinSig τr mname with
    | some ([τp], _) => τa != τp
    | _ => false
  | _, _ => false

mutual

/-- Refutation: is there a call anywhere on the fragment's spine that the table
    refutes? Recursion stops at any construct outside the fragment, so an
    unsupported node hides everything below it — the conservative direction. -/
def illTyped (e : Expr) : Bool :=
  match e with
  | .seq es => illTypedAny es
  | .if' c t els =>
    illTyped c || illTyped t || (match els with | some e' => illTyped e' | none => false)
  | .while' c b => illTyped c || illTyped b
  | .vasgn _ _ rhs => illTyped rhs
  | .send (some r) mname [a] none =>
    illTyped r || illTyped a || tableRefutes r mname a
  | _ => false
termination_by sizeOf e

def illTypedAny (es : List Expr) : Bool :=
  match es with
  | [] => false
  | e :: rest => illTyped e || illTypedAny rest
termination_by sizeOf es

end

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

/-- The verdict lattice. `accept` is backed by `check_sound`; `reject` is backed
    by the difftest direction `reject ⇒ srb rejects` (not by a theorem — see the
    refutation-pass header); `unknown` claims nothing and is the default. -/
inductive Verdict where
  | accept
  | reject
  | unknown
deriving DecidableEq, Repr, Inhabited

/-- **The checker.** Total and executable. `infer` is consulted first, so a
    program the type rules accept is never refuted; `illTyped` only ever
    upgrades an `unknown` to a `reject`. -/
def check (p : Expr) : Verdict :=
  match infer [] p with
  | some _ => .accept
  | none => if illTyped p then .reject else .unknown

/-! ## Worked verdicts

Each `unknown` below is *incompleteness* — `srb` rejects and we abstain — which
the ratchet permits and the pinned zero does not count. Each `reject` agrees
with `srb` [V, 0.6.13405].
-/

/-- `1 + nil` — srb 7002. The motivating case. -/
example : check (.send (some (.int 1)) "+" [.nil] none) = .reject := by
  simp [check, infer, illTyped, tableRefutes, defTy, builtinSig]

/-- `1 + true` — srb 7002. -/
example : check (.send (some (.int 1)) "+" [.tru] none) = .reject := by
  simp [check, infer, illTyped, tableRefutes, defTy, builtinSig]

/-- **Rejected, and perfectly safe.** `if false then 1 + nil else 0 end` runs to
    `0`. `reject` claims our rules refute the program, *not* that it fails —
    the asymmetry of `typed-portion-safety.md` §8.1. srb rejects this too, but
    for a different reason (7006 unreachable, not 7002), which is worth
    remembering when the difftest starts comparing diagnostics [V]. -/
example :
    check (.if' .fls (.send (some (.int 1)) "+" [.nil] none) (some (.int 0)))
      = .reject := by
  simp [check, infer, inferIf, illTyped, tableRefutes, defTy, builtinSig]

/-- `1 / 2` — srb *accepts*; `/` is absent from the table, so we abstain. This
    is the case that makes "absent ⇒ no opinion" mandatory rather than merely
    conservative: rejecting here would break `reject ⇒ srb rejects`. -/
example : check (.send (some (.int 1)) "/" [.int 2] none) = .unknown := by
  simp [check, infer, illTyped, tableRefutes, defTy, builtinSig]

/-- `1.foo(2)` — srb 7003. We abstain: the table cannot distinguish "no such
    method" from "method we have not tabulated". Incompleteness. -/
example : check (.send (some (.int 1)) "foo" [.int 2] none) = .unknown := by
  simp [check, infer, illTyped, tableRefutes, defTy, builtinSig]

/-- `q = 1; q + nil` — srb 7002. We abstain because `defTy` has no environment,
    so a local has no unconditional type. The obvious next widening. -/
example :
    check (.seq [ .vasgn .lvar "q" (.int 1),
                  .send (some (.var .lvar "q")) "+" [.nil] none ]) = .unknown := by
  simp [check, infer, inferSeq, illTyped, illTypedAny, tableRefutes, defTy,
    builtinSig, envSet, envGet?]

end RubyCore.Types
