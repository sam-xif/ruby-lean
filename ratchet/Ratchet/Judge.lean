import Ratchet.Expr
import Ratchet.Ty

/-!
# `Judge` — the hand-authored typing judgment

The **specification** half of the checker. `Ratchet/Validate.lean`'s `chk` is a
decision procedure; this file says *what it is deciding*. The split matters for the
ratchet: a rung is only honestly "climbed" when there is a derivation
`Judge Γ p τ Γ'` one can read and check by eye, not merely a `Bool` that came out
`true`.

## Scope: tiers 1–3, and no more

Deliberately authored for the rungs reached so far (tier 1's eight literals, tier 2's
`send`-shaped rungs, tier 3's `var`/`vasgn`/`seq`/bare-`vcall`), and nothing else.
Consequences, each a real limitation to lift later, not an oversight:

- **The environment threads, and it is flat.** `Judge Γ e τ Γ'` reads: *in local
  environment `Γ`, `e` synthesizes `τ` and leaves `Γ'` behind*. The output environment
  is what makes `x = 1; x = true; x` typeable — an assignment is an expression whose
  effect on the environment the next expression sees. It is deliberately a *flat*
  `List (String × Ty)` with `envSet` overwriting in place: real Ruby locals are not
  single-typed, so re-binding a name at a different type is correct behaviour, not a
  gap (rung `reassign-different-type`).
- **Locals only.** Rules mention `VarKind.lvar` explicitly; `@ivar`/`@@cvar`/`$gvar`
  are tiers 7+ and have no rule, so a program touching one is simply not typed.
- **No `subTy` anywhere.** Every rule below matches types by construction. `subTy`
  exists in `Ratchet/Ty.lean` and is unused here on purpose: with no parameters, there
  is nothing yet for subsumption to do, and a subsumption rule admitted "for later" is
  a rule whose soundness nobody has had to justify against a rung.
- **No `if`/join, no `def`, no dispatch.** Tiers 4–10. That absence is *load-bearing*
  for `BareNameError` below — see its docstring.
- **Top-level `self`.** Every judged program runs at the top-level object, because no
  rule types a `def'`/`class'`/`module'`/block body. Two rules quietly depend on this
  (`prim`'s "explicit receiver only" restriction, and `bareName`), and both would need
  a `self` type in the judgment the moment that changes.

## Every rule is a synthesis rule

There is exactly one kind of rule here: a **synthesis rule justified by the real
semantics** — a literal's type, or a primitive's signature (`PrimSig`). §Justification
in `AGENTS.md`'s tier-1/2 notes plus `Check13.lean`'s semantic cross-check are what back
them.

There used to be a second kind: a `claim` leaf admitting whatever a certificate asserted
about a subterm. It was the certificate architecture's trusted edge, and it was *unsound
in general* — a cert could claim anything, so a `Judge` derivation using it asserted
nothing. **It is gone** (2026-08-31), along with `Cert` itself: `Judge` now relates an
`Expr` to a `Ty` with nothing trusted in between, so *every* derivation in this package
is built only from rules that say something checkable about the real semantics, and a
rung is climbed only when the checker really can synthesize it. See `AGENTS.md`
§Claim-free.
-/

namespace Ratchet

/-- The receiver types for which `==` is a **total** method — it answers a boolean for
*any* argument and never raises.

Needed because `PrimSig.objEq` is the ladder's first rule that is polymorphic in an
argument type (`1 == "a"` is safe Ruby, rung 021), and a rule that generous should say
out loud which receivers it is claiming this for. Every class listed here inherits
`Object#==` (or overrides it with an equally total one: `Integer#==`, `String#==`,
`NilClass#==`, `Symbol#==`, `Float#==`), all of which answer `false` on an unrelated
argument rather than raising.

Deliberately *not* including `.any`: `.any` also denotes a `BasicObject`, and while
`BasicObject#==` does exist, nothing in the corpus needs it and admitting `.any` here
would make the rule unfalsifiable by any rung. -/
inductive EqSafe : Ty → Prop
  | int : EqSafe .int
  | float : EqSafe .float
  | bool : EqSafe .bool
  | nilT : EqSafe .nilT
  | sym : EqSafe .sym
  /-- Any named class: `Object#==` is inherited by every one of them. -/
  | cls {n : String} : EqSafe (.cls n)

/-- The primitive-method signature table, as a **relation** with one constructor per
justified builtin. A relation rather than a function because this is the specification:
each constructor is a claim about what the real `stepFn` does, to be read and checked
one at a time. `Ratchet/Validate.lean`'s `primSig?` is the executable version, proved
to only ever produce a `PrimSig` (`primSig?_sound`).

Every constructor here is a signature for a **total** method on the given argument
types: for these receiver/argument combinations, CRuby (and `RubyCore`'s `Builtins`)
neither raises nor coerces, and the result class is fixed. Deliberately *narrow*: no
`Integer#+ Float`, no `String#*`, no `Integer#to_s(base)` — a signature is added when a
rung needs it and its result has been checked against the semantics, not because it
looks obviously true. -/
inductive PrimSig : Ty → String → List Ty → Ty → Prop
  /-- `Integer#+ (Integer) → Integer` (rung 009). -/
  | intAdd : PrimSig .int "+" [.int] .int
  /-- `Integer#- (Integer) → Integer` (rung 010). -/
  | intSub : PrimSig .int "-" [.int] .int
  /-- `Integer#* (Integer) → Integer` (rung 011). -/
  | intMul : PrimSig .int "*" [.int] .int
  /-- `Integer#/ (Integer) → Integer` (rung 012).

      **Note what this does and does not claim.** `10 / 0` raises `ZeroDivisionError`,
      so this signature is *not* "never raises" — it is the weaker, and correct,
      "never reaches the `NoMethodError`/`ArgumentError`/`TypeError` family, and when it
      returns, returns an `Integer`". That is exactly the reading of type-safety this
      whole ladder uses (`AGENTS.md` §Design notes), and division is the cleanest place
      in the corpus where the two readings come apart. A checker built on the stronger
      reading would have to reject `10 / 2`, which would be wrong. -/
  | intDiv : PrimSig .int "/" [.int] .int
  /-- `String#+ (String) → String` (rung 013). Argument type is load-bearing:
      `"a" + 1` really does raise `TypeError` ("no implicit conversion"), which is *in*
      the family — hence `[.cls "String"]`, not `[.any]`. -/
  | strAdd : PrimSig (.cls "String") "+" [.cls "String"] (.cls "String")
  -- ### Tier 2's second half (rungs 014–028)
  --
  -- Five more shapes, each a different *reason* a signature is admissible, which is why
  -- they are worth reading one at a time rather than as a table:
  --
  -- - a **comparison** returns a `Bool` while still constraining its argument (`1 < "a"`
  -- raises `ArgumentError`, which is in the family — so the `[.int]` is load-bearing,
  -- exactly as in `strAdd`);
  -- - a **nullary total query** (`to_s`, `zero?`, `length`) constrains nothing but the
  -- receiver;
  -- - **`!`** is an ordinary send in Ruby, not syntax — the desugarer emits
  -- `send (tru) "!" []` — so negation needs no new `Expr` node, only a row;
  -- - **`==`** is the first rule polymorphic in its argument (see `EqSafe`).
  /-- `Integer#< (Integer) → Bool` (rung 014). -/
  | intLt : PrimSig .int "<" [.int] .bool
  /-- `Integer#<= (Integer) → Bool` (rung 024). -/
  | intLe : PrimSig .int "<=" [.int] .bool
  /-- `Integer#> (Integer) → Bool`. Admitted alongside `<` because the ladder's
      soundness argument for it is character-for-character the same one. -/
  | intGt : PrimSig .int ">" [.int] .bool
  /-- `Integer#>= (Integer) → Bool` (rung 025). -/
  | intGe : PrimSig .int ">=" [.int] .bool
  /-- `Integer#to_s () → String` (rung 019). Zero-argument only: `5.to_s(2)` (the base
      form) is also legal, but its signature is a different row nobody has needed, and
      admitting `[.int]` here would be a guess. -/
  | intToS : PrimSig .int "to_s" [] (.cls "String")
  /-- `Integer#zero? () → Bool` (rung 022). Total on every `Integer`. -/
  | intZeroP : PrimSig .int "zero?" [] .bool
  /-- `String#length () → Integer` (rung 028). -/
  | strLength : PrimSig (.cls "String") "length" [] .int
  /-- `!recv → Bool` for a boolean receiver (rung 015). Narrow on purpose: `!nil` and
      `!5` are equally safe in Ruby (`!` is total on *every* object), but a rule that
      broad would need `.any` on the receiver, and no rung asks for it yet. -/
  | notBool : PrimSig .bool "!" [] .bool
  /-- `recv == (anything) → Bool` (rungs 020, 021, 026). The argument type is
      unconstrained — this is the rule `AGENTS.md` §Design notes demands as
      `Object#== : (any) → Bool`: `1 == "a"` is perfectly safe Ruby answering `false`,
      so requiring both sides to have the same `Ty` would be a conservative *choice*,
      not a soundness requirement. The receiver still has to be `EqSafe`. -/
  | objEq {σ τ : Ty} : EqSafe σ → PrimSig σ "==" [τ] .bool

/-- The bare names that resolve to **no method at all** at top-level `self`, so that
evaluating them raises `NameError`.

A table with one row per justified name, exactly like `PrimSig` — and, like `PrimSig`,
the *narrowness* is the point. It is tempting to write a single rule "a bare identifier
is `.any`, because an undefined one raises `NameError`, and `NameError` is outside the
`NoMethodError`/`ArgumentError`/`TypeError` family this ladder calls type-stuck". That
rule is **unsound**: a bare identifier need not be undefined. `proc` and `lambda` are
private `Kernel` methods, and evaluating either with no block raises `ArgumentError`,
which is squarely in the family. `puts`, `rand`, `raise`, `loop`, … are all reachable
the same way. So the checker cannot assume a bare name is unbound; it has to be told,
per name, and each row is a claim checkable by running the program
(`CheckRungs.lean` does exactly that, and `proc`/`lambda` are negative controls).

Two things make even the one row below sound, and both are properties of the *current*
judgment rather than of Ruby, so both are due for revisiting:

- **No rule types a `def'`.** A program that defines `x` and then calls it bare cannot
  be judged at all, because the `def'` statement inside the `seq` has no rule — so
  `bareName` can never launder a user-defined method whose body is type-stuck. The rung
  that adds `def'` (tier 6) must therefore either delete this rule or gate it on the
  program's declaration table.
- **Top-level `self`.** Inside a method or class body a bare name resolves against a
  different receiver; the judgment has no `self` yet (see the module docstring). -/
inductive BareNameError : String → Prop
  /-- `x` (rung `bare-undeclared-var`): not a `Kernel` method, not a local, so `NameError`. -/
  | x : BareNameError "x"

mutual

/-- `Judge Γ e τ Γ'`: in local environment `Γ`, the expression `e` synthesizes type `τ`
and leaves environment `Γ'`. Nothing is trusted — see the module docstring.

Read each literal rule as an assertion about the real semantics: evaluating this literal
yields a value whose class is the one `τ` names. `CheckRungs.lean` checks precisely that,
by running the actual `stepFn`.

The environment threads left-to-right through every compound rule, in evaluation order.
For the rules below tier 3 that is invisible (a literal returns `Γ` unchanged), but it
is *not* cosmetic even at tier 2: Ruby evaluates a send's receiver before its arguments
and its arguments left to right, and each of them may contain an assignment, so `prim`
threads `Γ → Γ₁ → Γ₂` rather than typing all three parts in the same `Γ`. -/
inductive Judge : Env → Expr → Ty → Env → Prop
  /-- An integer literal — including a negative one: `-5` desugars to `int (-5)`, not to
      a unary send (rung 008), so this single rule covers both. -/
  | intLit {Γ : Env} {n : Int} : Judge Γ (.int n) .int Γ
  /-- A float literal. `Expr.flt` carries IEEE bits; the type does not depend on them,
      so no side condition. -/
  | fltLit {Γ : Env} {bits : UInt64} : Judge Γ (.flt bits) .float Γ
  /-- A string literal is *an instance of* `String` — `.cls "String"`, never a
      dedicated `str` type; this type language has none (`Ratchet/Ty.lean`). -/
  | strLit {Γ : Env} {s : String} : Judge Γ (.str s) (.cls "String") Γ
  | symLit {Γ : Env} {s : String} : Judge Γ (.sym s) .sym Γ
  /-- `true` and `false` share one type. `Ty` has no singleton-`true` type, and Ruby's
      two distinct classes (`TrueClass`/`FalseClass`) are not distinguished here —
      `Ty.bool` covers both, which is why rungs 002 and 003 both target `.bool`. -/
  | truLit {Γ : Env} : Judge Γ .tru .bool Γ
  | flsLit {Γ : Env} : Judge Γ .fls .bool Γ
  /-- `nil : Nil` — the singleton type, not `nilable` of anything. -/
  | nilLit {Γ : Env} : Judge Γ .nil .nilT Γ
  /-- Reading a local: its type is whatever the environment last recorded for it, and
      the read binds nothing. A name *not* in `Γ` has no rule — and correctly so, since
      the desugarer only emits `var lvar x` where Ruby's parser saw an assignment to `x`
      earlier in the same scope; a bare name it did not is a `vcall` (see `bareName`). -/
  | var {Γ : Env} {x : String} {τ : Ty} :
      envGet? Γ x = some τ → Judge Γ (.var .lvar x) τ Γ
  /-- Assignment. Its *value* is the right-hand side's (Ruby's `x = e` evaluates to `e`),
      and its *effect* is to record that type for `x` in the outgoing environment.

      `envSet` overwrites, so `x = 1; x = true` simply re-types `x`; nothing here demands
      the new type relate to the old one. That is not a weakness of the checker, it is
      what a Ruby local *is* (rung `reassign-different-type`). Note the ordering: the
      right-hand side is typed in `Γ` and may itself assign (`y = (x = 1) + 1`), so the
      binding is added to `Γ'`, the environment the RHS left behind — not to `Γ`. -/
  | vasgn {Γ Γ' : Env} {x : String} {e : Expr} {τ : Ty} :
      Judge Γ e τ Γ' → Judge Γ (.vasgn .lvar x e) τ (envSet Γ' x τ)
  /-- A statement sequence: the whole thing has the *last* statement's type, and the
      environment threads through all of them. Delegated to `JudgeSeq` so the
      non-empty requirement is structural. -/
  | seq {Γ Γ' : Env} {es : List Expr} {τ : Ty} :
      JudgeSeq Γ es τ Γ' → Judge Γ (.seq es) τ Γ'
  /-- A bare identifier that is not a local: `x` desugars to `vcall "x"`, a method-call
      attempt on implicit `self`. When the name resolves to nothing (`BareNameError`),
      evaluating it raises `NameError` — which is *outside* the
      `NoMethodError`/`ArgumentError`/`TypeError` family this ladder defines type-safety
      over, exactly as `ZeroDivisionError` is (see `PrimSig.intDiv`). So the program is
      type-safe despite crashing, and the type recorded is `.any`: the expression never
      produces a value, so nothing downstream can depend on it — and `.any` matches no
      `PrimSig` row and is not `EqSafe`, so no rule can consume it either. Type safety
      here is not crash-freedom, and this rung is the sharpest place that shows. -/
  | bareName {Γ : Env} {m : String} : BareNameError m → Judge Γ (.vcall m) .any Γ
  /-- `if c then t else e`. Three things about this rule are decisions, not defaults:

      **The condition's type is unconstrained.** `σ` appears nowhere in the conclusion.
      Ruby's `if` accepts *any* value and never raises over its condition's type — only
      `nil` and `false` are falsy — so a `Bool`-only premise would reject
      `if 5 … end` and `if nil … end`, both of which are perfectly safe (rungs
      `if-condition-not-bool`, `if-nil-condition`). The condition is still *typed*,
      because evaluating it can itself be type-stuck.

      **The result type is a total join.** `joinT` never fails: unrelated branches
      produce a `Ty.union` rather than a rejection (rung `if-branch-mismatch`).

      **The environments are joined too, and that is a soundness requirement.** A branch
      may rebind a local at a different type, and the code after the `if` sees whichever
      branch ran. Carrying `Γ` (the pre-`if` environment) forward instead would certify
      `corpus/042-if-does-not-leak-reassignment`, which really raises `TypeError`. So the
      outgoing environment is `joinEnv Γ₁ Γ₂`, and a name the two branches disagree about
      ends up at a union that no rule can consume. -/
  | if' {Γ Γc Γ₁ Γ₂ : Env} {c t e : Expr} {σ τ₁ τ₂ : Ty} :
      Judge Γ c σ Γc → Judge Γc t τ₁ Γ₁ → Judge Γc e τ₂ Γ₂ →
      Judge Γ (.if' c t (some e)) (joinT τ₁ τ₂) (joinEnv Γ₁ Γ₂)
  /-- `if c then t end`, with no `else`. Ruby's missing branch evaluates to `nil`, so
      this is the same rule with the else-branch's type fixed at `.nilT` and its
      environment fixed at `Γc` — the environment as of the end of the condition.
      `joinT τ .nilT` is `mkNilable τ` (rung `if-no-else`). -/
  | ifNoElse {Γ Γc Γ₁ : Env} {c t : Expr} {σ τ : Ty} :
      Judge Γ c σ Γc → Judge Γc t τ Γ₁ →
      Judge Γ (.if' c t none) (joinT τ .nilT) (joinEnv Γ₁ Γc)
  /-- An explicit-receiver, block-less `send` whose receiver and arguments type, and
      whose resulting shape has a justified `PrimSig`.

      Three restrictions are each doing work: `some recv` (an implicit-self send has
      nobody to dispatch on in this fragment), `blk = none` (a block would need
      `Expr.block` typing, tier ≥ 9), and `PrimSig` matching the *synthesized* argument
      types exactly (no subsumption — see the module docstring). -/
  | prim {Γ Γ₁ Γ₂ : Env} {recv : Expr} {m : String} {args : List Expr}
      {σ τ : Ty} {argTys : List Ty} :
      Judge Γ recv σ Γ₁ → JudgeAll Γ₁ args argTys Γ₂ → PrimSig σ m argTys τ →
      Judge Γ (.send (some recv) m args none) τ Γ₂

/-- Pointwise `Judge` over an argument list, with matching length by construction and
the environment threaded left to right (Ruby's argument evaluation order). -/
inductive JudgeAll : Env → List Expr → List Ty → Env → Prop
  | nil {Γ : Env} : JudgeAll Γ [] [] Γ
  | cons {Γ Γ₁ Γ₂ : Env} {e : Expr} {es : List Expr} {τ : Ty} {τs : List Ty} :
      Judge Γ e τ Γ₁ → JudgeAll Γ₁ es τs Γ₂ → JudgeAll Γ (e :: es) (τ :: τs) Γ₂

/-- A non-empty statement sequence. The result type is the last statement's; every
earlier statement must still type (a statement nobody reads can still be type-stuck),
and each one's outgoing environment is the next one's incoming. -/
inductive JudgeSeq : Env → List Expr → Ty → Env → Prop
  | last {Γ Γ' : Env} {e : Expr} {τ : Ty} : Judge Γ e τ Γ' → JudgeSeq Γ [e] τ Γ'
  | cons {Γ Γ₁ Γ₂ : Env} {e e' : Expr} {es : List Expr} {σ τ : Ty} :
      Judge Γ e σ Γ₁ → JudgeSeq Γ₁ (e' :: es) τ Γ₂ → JudgeSeq Γ (e :: e' :: es) τ Γ₂

end

end Ratchet
