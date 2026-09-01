import Ratchet.Expr
import Ratchet.Ty

/-!
# `Judge` — the hand-authored typing judgment

The **specification** half of the checker. `Ratchet/Validate.lean`'s `chk` is a
decision procedure; this file says *what it is deciding*. The split matters for the
ratchet: a rung is only honestly "climbed" when there is a derivation
`Judge Γ p τ Γ'` one can read and check by eye, not merely a `Bool` that came out
`true`.

## Scope: tiers 1–5, and no more

Deliberately authored for the rungs reached so far (tier 1's eight literals, tier 2's
`send`-shaped rungs, tier 3's `var`/`vasgn`/`seq`/bare-`vcall`, tier 4's conditionals,
tier 5's array and hash literals and their `#[]`), and nothing else.
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
- **No `def`, no dispatch, no user classes.** Tiers 6–10. The absence of a `def'` rule
  is *load-bearing* for `BareNameError` below — see its docstring.
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
  -- ### Tier 5's two indexing rows
  --
  -- Ruby has no index *syntax*: `a[0]` is `send a "[]" [0]`, an ordinary method call, so
  -- indexing needs no new `Expr` node and no new rule shape — only these two rows. What
  -- makes them worth reading one at a time is that each one's *result* is where the
  -- interesting claim lives, not its argument list.
  /-- `Array#[] (Integer) → nilable elem` (rung `array-index`).

      **Why `nilable` and not `elem`.** An in-range index gives an element; an
      out-of-range one gives `nil` (`[1,2,3][99]` is `nil`, not an error). The checker
      cannot tell which without arithmetic on the index and a length it does not track,
      so the honest result type is the one that covers both. The cost is real and visible:
      `[1,2,3][0] + 1` is safe Ruby that this rule makes untypeable, because
      `nilable Int` matches no arithmetic row. It is kept as a negative control
      (`CheckRungs.lean`) so the imprecision is recorded rather than forgotten.

      **Why `[.int]` is load-bearing.** `[1,2,3]["a"]` raises `TypeError` ("no implicit
      conversion of String into Integer") — inside the family — so an `.any` argument
      here would be unsound, exactly as in `strAdd`. Also a negative control.

      **What it does not claim.** `[1,2,3][2**70]` raises `RangeError` ("bignum too big
      to convert into `long`"). Like `intDiv`'s `ZeroDivisionError`, that is *outside* the
      `NoMethodError`/`ArgumentError`/`TypeError` family this ladder defines type-safety
      over, so the row stands; it claims "never type-stuck, and returns `elem` or `nil`",
      not "never raises". -/
  | arrayIndex {τ : Ty} : PrimSig (.arrayOf τ) "[]" [.int] (mkNilable τ)
  /-- `Hash#[] (anything) → any` (rung `hash-index`).

      **The argument is unconstrained** for the same reason `objEq`'s is: `Hash#[]` looks
      the key up by `hash`/`eql?`, both of which every class in this `Ty` has totally
      inherited from `Object`, and a missing key answers `nil` rather than raising
      (`{"a"=>1}["z"]` is `nil`; `{"a"=>1}[[1,2]]` is `nil`). So there is no key type
      this rule needs to exclude.
      
      **The result is `.any` because `Ty` cannot say better.** There is no `hashOf`
      constructor to read a value type back off — `hashLit` types every hash as the bare
      `.cls "Hash"` — so the value's type is genuinely unknown here, and `.any` is the
      only sound answer. It is also inert (no `PrimSig` row has an `.any` receiver, and
      `.any` is not `EqSafe`), so nothing downstream can consume what the checker does not
      know. This row is the sharpest statement of the `Ty` gap the `hash-lit` rung
      records: `{"a"=>1}["a"] + 1` is safe Ruby that no rule can type. -/
  | hashIndex {τ : Ty} : PrimSig (.cls "Hash") "[]" [τ] .any

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

/-! ## Tier 6's two tables

A top-level `def` puts a *method* into the world, and nothing in `Env` can hold one: a
method has parameters and a body, not a type. So tier 6 adds two tables beside `Env`, and
they are as different from each other as they are from `Env`.

`DefTable` is **syntax the checker has seen**; `AsmTable` is **a claim the checker is in
the middle of discharging**. Neither is trusted, but for opposite reasons: the first
because it is read straight off the program, the second because the only rule that adds to
it also proves it. -/

/-- One top-level method definition, as the checker sees it: a name, a parameter list and
a body — no types anywhere, because none are written in Ruby. -/
structure Defn where
  name : String
  params : List Param
  body : Expr

/-- The methods **already defined at this point in evaluation order**.

The "already" is a soundness requirement, not bookkeeping. Collecting every `def` in the
program up front would certify `foo(); def foo; end`, which raises `NoMethodError` — the
headline member of the family this ladder calls type-stuck. So `D` is threaded through
`JudgeSeq` (see `extendDefs`) exactly the way `Env` is threaded through everything, and a
call can only see a `def` that a *preceding* statement performed.

Note what that costs and does not cost: a `def` inside an `if` branch never reaches the
table (`extendDefs` looks only at a statement head), so a program that calls such a method
is simply not typed. Conservative, and no rung asks for it. What it does *not* cost is
forward reference **inside a body**: `def twice(x) = inc(inc(x))` type-checks against
whatever `D` holds at the *call site* of `twice`, which is after every top-level `def` has
run — so source order between two `def`s is irrelevant (rung `fun-calling-another-fun`),
while source order between a `def` and a call is not. -/
abbrev DefTable := List Defn

def defGet? (D : DefTable) (m : String) : Option Defn := D.find? (·.name == m)

/-- `D` after performing statement `e`: one entry longer if `e` is a top-level `def`,
unchanged otherwise. -/
def extendDefs (D : DefTable) : Expr → DefTable
  | .def' n ps body => ⟨n, ps, body⟩ :: D
  | _ => D

/-- One **assumed** instantiation: "a call to `name` whose arguments synthesize `argTys`
returns `ret`". Keyed by the argument types, not just the name, because this checker types
a body once per call-site shape (see `Judge.callDef`) rather than inferring one signature
per method. -/
structure Asm where
  name : String
  argTys : List Ty
  ret : Ty

/-- The instantiations currently **assumed**, to break the cycle a recursive method
creates.

**Read a `Judge D Δ Γ e τ Γ'` with a non-empty `Δ` as a *conditional* claim** — "if every
assumption in `Δ` holds, then `e : τ`". Only `Δ = []` is an absolute one, and `validate`
starts there. `Judge.callAsm` on its own is therefore blatantly unsound (`Δ` could say
anything); what makes the whole judgment sound is that `Judge.callDef` is the *only* rule
that ever extends `Δ`, and it discharges what it adds. -/
abbrev AsmTable := List Asm

def asmGet? (Δ : AsmTable) (m : String) (τs : List Ty) : Option Ty :=
  (Δ.find? (fun a => a.name == m && a.argTys == τs)).map (·.ret)

/-- The environment a method body starts in: **only** its parameters, bound to the
argument types the call site synthesized. `none` unless every parameter is required and
the counts match.

Two decisions in one small function:

- **A fresh environment, not the caller's.** A Ruby method body does not see the caller's
  locals, so the body is judged in `paramEnv`'s result and the call's *outgoing*
  environment is the caller's own (after the arguments), never the body's.
- **Required parameters only.** `Param.opt`/`.rest`/`.key`/`.kwrest`/`.block` all answer
  `none`, so a method using one is not typed at all. That is the arity gap `AGENTS.md`
  §Frontier item 3 names; a conservative `none` here is the honest placeholder, and
  `CheckRungs.lean` carries `def f(x = 1); x; end; f()` as a control so the cost is
  measured. Length mismatch is also `none`, which is what rejects `fun-wrong-arity`. -/
def paramEnv : List Param → List Ty → Option Env
  | [], [] => some []
  | .req x :: ps, τ :: τs => (paramEnv ps τs).map (fun Γ => (x, τ) :: Γ)
  | _, _ => none

mutual

/-- `Judge D Δ Γ e τ Γ'`: with methods `D` defined and instantiations `Δ` assumed, in
local environment `Γ` the expression `e` synthesizes type `τ` and leaves environment `Γ'`
Nothing is trusted — see the module docstring, and `AsmTable` for what a non-empty `Δ`
means.

Read each literal rule as an assertion about the real semantics: evaluating this literal
yields a value whose class is the one `τ` names. `CheckRungs.lean` checks precisely that,
by running the actual `stepFn`.

The environment threads left-to-right through every compound rule, in evaluation order.
For the rules below tier 3 that is invisible (a literal returns `Γ` unchanged), but it
is *not* cosmetic even at tier 2: Ruby evaluates a send's receiver before its arguments
and its arguments left to right, and each of them may contain an assignment, so `prim`
threads `Γ → Γ₁ → Γ₂` rather than typing all three parts in the same `Γ`. -/
inductive Judge : DefTable → AsmTable → Env → Expr → Ty → Env → Prop
  /-- An integer literal — including a negative one: `-5` desugars to `int (-5)`, not to
      a unary send (rung 008), so this single rule covers both. -/
  | intLit {D : DefTable} {Δ : AsmTable} {Γ : Env} {n : Int} : Judge D Δ Γ (.int n) .int Γ
  /-- A float literal. `Expr.flt` carries IEEE bits; the type does not depend on them,
      so no side condition. -/
  | fltLit {D : DefTable} {Δ : AsmTable} {Γ : Env} {bits : UInt64} : Judge D Δ Γ (.flt bits) .float Γ
  /-- A string literal is *an instance of* `String` — `.cls "String"`, never a
      dedicated `str` type; this type language has none (`Ratchet/Ty.lean`). -/
  | strLit {D : DefTable} {Δ : AsmTable} {Γ : Env} {s : String} : Judge D Δ Γ (.str s) (.cls "String") Γ
  | symLit {D : DefTable} {Δ : AsmTable} {Γ : Env} {s : String} : Judge D Δ Γ (.sym s) .sym Γ
  /-- `true` and `false` share one type. `Ty` has no singleton-`true` type, and Ruby's
      two distinct classes (`TrueClass`/`FalseClass`) are not distinguished here —
      `Ty.bool` covers both, which is why rungs 002 and 003 both target `.bool`. -/
  | truLit {D : DefTable} {Δ : AsmTable} {Γ : Env} : Judge D Δ Γ .tru .bool Γ
  | flsLit {D : DefTable} {Δ : AsmTable} {Γ : Env} : Judge D Δ Γ .fls .bool Γ
  /-- `nil : Nil` — the singleton type, not `nilable` of anything. -/
  | nilLit {D : DefTable} {Δ : AsmTable} {Γ : Env} : Judge D Δ Γ .nil .nilT Γ
  /-- Reading a local: its type is whatever the environment last recorded for it, and
      the read binds nothing. A name *not* in `Γ` has no rule — and correctly so, since
      the desugarer only emits `var lvar x` where Ruby's parser saw an assignment to `x`
      earlier in the same scope; a bare name it did not is a `vcall` (see `bareName`). -/
  | var {D : DefTable} {Δ : AsmTable} {Γ : Env} {x : String} {τ : Ty} :
      envGet? Γ x = some τ → Judge D Δ Γ (.var .lvar x) τ Γ
  /-- Assignment. Its *value* is the right-hand side's (Ruby's `x = e` evaluates to `e`),
      and its *effect* is to record that type for `x` in the outgoing environment.

      `envSet` overwrites, so `x = 1; x = true` simply re-types `x`; nothing here demands
      the new type relate to the old one. That is not a weakness of the checker, it is
      what a Ruby local *is* (rung `reassign-different-type`). Note the ordering: the
      right-hand side is typed in `Γ` and may itself assign (`y = (x = 1) + 1`), so the
      binding is added to `Γ'`, the environment the RHS left behind — not to `Γ`. -/
  | vasgn {D : DefTable} {Δ : AsmTable} {Γ Γ' : Env} {x : String} {e : Expr} {τ : Ty} :
      Judge D Δ Γ e τ Γ' → Judge D Δ Γ (.vasgn .lvar x e) τ (envSet Γ' x τ)
  /-- A statement sequence: the whole thing has the *last* statement's type, and the
      environment threads through all of them. Delegated to `JudgeSeq` so the
      non-empty requirement is structural, and because `JudgeSeq` is also where the *def
      table* threads (a `def` is visible to the statements after it and to nothing else —
      see `DefTable`). -/
  | seq {D : DefTable} {Δ : AsmTable} {Γ Γ' : Env} {es : List Expr} {τ : Ty} :
      JudgeSeq D Δ Γ es τ Γ' → Judge D Δ Γ (.seq es) τ Γ'
  /-- A bare identifier that is not a local: `x` desugars to `vcall "x"`, a method-call
      attempt on implicit `self`. When the name resolves to nothing (`BareNameError`),
      evaluating it raises `NameError` — which is *outside* the
      `NoMethodError`/`ArgumentError`/`TypeError` family this ladder defines type-safety
      over, exactly as `ZeroDivisionError` is (see `PrimSig.intDiv`). So the program is
      type-safe despite crashing, and the type recorded is `.any`: the expression never
      produces a value, so nothing downstream can depend on it — and `.any` matches no
      `PrimSig` row and is not `EqSafe`, so no rule can consume it either. Type safety
      here is not crash-freedom, and this rung is the sharpest place that shows.

      **The `defGet? D m = none` premise is tier 6's doing, and it was predicted.** Until
      tier 6 no rule typed a `def'`, so a program that defined `x` and then called it bare
      could not be judged at all, and that accident was what made the one `BareNameError`
      row sound. Tier 6 types `def'`, so the accident is gone: without this premise,
      `def x; 1 + true; end; x` would take the `bareName` route to `.any` and validate a
      program that raises `TypeError`. The premise restores the property by *checking* it
      instead of relying on it — a bare name is a `NameError` only if nothing has defined
      it. `CheckRungs.lean` carries exactly that program as a control.

      Note the shape of the remaining conservatism: there is no rule for a `vcall` that
      *does* name a defined method (`def get5; 5; end; get5`, no parentheses), because the
      desugarer emits a `vcall` rather than an argument-less `send` there and no rung asks
      for it. Such a program is simply not typed. -/
  | bareName {D : DefTable} {Δ : AsmTable} {Γ : Env} {m : String} :
      BareNameError m → defGet? D m = none → Judge D Δ Γ (.vcall m) .any Γ
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
      Judge D Δ Γ c σ Γc → Judge D Δ Γc t τ₁ Γ₁ → Judge D Δ Γc e τ₂ Γ₂ →
      Judge D Δ Γ (.if' c t (some e)) (joinT τ₁ τ₂) (joinEnv Γ₁ Γ₂)
  /-- `if c then t end`, with no `else`. Ruby's missing branch evaluates to `nil`, so
      this is the same rule with the else-branch's type fixed at `.nilT` and its
      environment fixed at `Γc` — the environment as of the end of the condition.
      `joinT τ .nilT` is `mkNilable τ` (rung `if-no-else`). -/
  | ifNoElse {D : DefTable} {Δ : AsmTable} {Γ Γc Γ₁ : Env} {c t : Expr} {σ τ : Ty} :
      Judge D Δ Γ c σ Γc → Judge D Δ Γc t τ Γ₁ →
      Judge D Δ Γ (.if' c t none) (joinT τ .nilT) (joinEnv Γ₁ Γc)
  /-- An array literal. The elements are typed left to right — `JudgeAll` already
      threads the environment in exactly Ruby's element-evaluation order, so this rule
      needs no new machinery beyond `elemTy` — and the literal's type is `arrayOf` of
      their join.

      **Every element must type, including ones whose type is then thrown away.** The
      join can widen `[1, "a"]` to `arrayOf (union Int String)`, but it cannot excuse an
      element that is itself type-stuck: `[1, 1 + "a"]` has no derivation, because
      `JudgeAll` demands a type for each element (rung `array-of-sends` is the positive
      form of the same point — `[1 + 1, 2 + 2]` types only because its elements do).

      **`arrayOf` is invariant** (`Ratchet/Ty.lean`), and this rule is where that matters
      eventually rather than now: covariance is unsound under mutation-through-aliasing,
      and there is as yet no rule for `Array#<<` or `Array#[]=`. Whichever tier adds one
      inherits the obligation. -/
  | arrayLit {D : DefTable} {Δ : AsmTable} {Γ Γ' : Env} {es : List Expr} {τs : List Ty} :
      JudgeAll D Δ Γ es τs Γ' → Judge D Δ Γ (.array es) (.arrayOf (elemTy τs)) Γ'
  /-- A hash literal, typed as the bare `.cls "Hash"`.

      **The key and value types are discarded, and the premise is still not vacuous.**
      `Ty` has no parameterised hash constructor (no `hashOf` beside `arrayOf`), so there
      is nowhere to record what a hash maps to — but every key and every value expression
      must still be *typeable*, because evaluating one can be type-stuck all on its own
      (`{"a" => 1 + "b"}` must not type). `JudgePairs` is what carries that requirement,
      and it also threads the environment in Ruby's order: key then value, pair by pair.

      This is the rung the corpus records as a `Ty` language gap rather than a missing
      rule, and `PrimSig.hashIndex` is where the gap becomes visible. -/
  | hashLit {D : DefTable} {Δ : AsmTable} {Γ Γ' : Env} {pairs : List (Expr × Expr)} :
      JudgePairs D Δ Γ pairs Γ' → Judge D Δ Γ (.hash pairs) (.cls "Hash") Γ'
  /-- A top-level `def` **statement**. Its type is `.sym`: `def foo; end` evaluates to
      `:foo` in Ruby, which is easy to forget because nobody uses the value.

      **The body is not checked here, and that is correct rather than lazy.** A method that
      is never called never runs, so `def bad(x); x + true; end` with no call site is
      perfectly safe Ruby and validates. What the rule *does* is nothing at all to the
      environment — a `def` binds no local — while `JudgeSeq.cons` separately extends `D`
      with it (see `extendDefs`). Keeping those two effects in different places is
      deliberate: the type of a `def` is a fact about the expression, whereas its effect on
      `D` is a fact about *statement order*, and only `JudgeSeq` knows about order.

      The body's obligation arrives instead at each call site, via `callDef`. -/
  | defStmt {D : DefTable} {Δ : AsmTable} {Γ : Env} {n : String}
      {ps : List Param} {body : Expr} :
      Judge D Δ Γ (.def' n ps body) .sym Γ
  /-- A call to a method whose instantiation is **assumed**.

      On its own this rule is unsound in the most obvious way: `Δ` is an index, so a
      derivation may start from any `Δ` at all. It is sound *in context* because
      `callDef` below is the only rule that ever grows `Δ`, and it grows it by exactly the
      assumption it then discharges — so a derivation at `Δ = []`, which is where
      `validate` starts, contains no undischarged assumption. See `AsmTable`.

      The lookup is keyed by the argument types as well as the name, because this checker
      has no notion of "the" signature of a method: it types a body once per call-site
      argument shape. -/
  | callAsm {D : DefTable} {Δ : AsmTable} {Γ Γ' : Env} {m : String}
      {args : List Expr} {argTys : List Ty} {ρ : Ty} :
      JudgeAll D Δ Γ args argTys Γ' → asmGet? Δ m argTys = some ρ →
      Judge D Δ Γ (.send none m args none) ρ Γ'
  /-- **A call to a defined method, with its body checked at this call site's argument
      types.** The centre of tier 6.

      *Ruby writes no parameter types anywhere*, so there is nothing to check a call
      against: `def add(x, y) = x + y` has no signature until someone calls it. This rule's
      answer is to not have signatures at all — the body is judged in `paramEnv ps argTys`,
      a fresh environment holding just the parameters at the types the call site produced,
      and the call's type is whatever the body synthesizes there. Three consequences worth
      naming:

      - **Per-call-site, not per-method.** `add(1, 2)` and `add("a", "b")` are checked
        separately, and the second would need a `String#+` row rather than failing because
        of the first. This is closer to template instantiation than to Hindley–Milner, and
        it is why `fun-returning-array`'s parameters are "constrained only by the call
        site": nothing in `[x, y]` says what `x` is.
      - **The body's errors are found by looking through the `def`.** `fun-body-mismatch`
        (`def bad(x) = x + true; bad(1)`) is rejected here and nowhere else: the call site
        looks fine, and the `TypeError` is inside a body that only dispatch reaches.
      - **The caller's environment is untouched.** The outgoing environment is `Γ'` — the
        caller's, after the arguments — never the body's. A Ruby method body neither sees
        nor writes the caller's locals.

      **Recursion, and why the assumption is discharged rather than believed.** `fact`
      calls itself, so its body cannot be judged before its return type is known, and its
      return type comes from its body. The cycle is broken by *assume-then-verify*: `ρ`
      appears in the premise as an assumption (`(m, argTys, ρ) :: Δ`, which `callAsm` picks
      up at the recursive occurrence) **and** as the type the body must synthesize under
      that assumption. Nothing here says where `ρ` came from; `Ratchet/Validate.lean` finds
      a candidate by typing the body once with the recursive call at `.never` and then
      *re-runs* the check with the candidate in place. The first pass is an untrusted hint
      — a wrong hint fails the second pass — which is why no version of it appears in this
      rule.

      That the discharge is legitimate is an induction on the *execution*, not on the
      derivation: each use of `callAsm` inside the body corresponds to an actual recursive
      call one level deeper at run time, so "if the call returns, it returns a `ρ`" follows
      by induction on the number of calls that actually completed. A non-terminating
      recursion makes the claim vacuous, exactly as `PrimSig.intDiv` makes no claim about
      `ZeroDivisionError`. `CheckRungs.lean` carries the control that shows the second pass
      is load-bearing: `def f(x) = if x <= 0 then 1 else f(x-1) + true` really raises
      `TypeError`, and the *first* pass alone would have accepted it (the recursive call
      typed at `.never` makes the whole `else` branch `.never`, which the join then
      discards). -/
  | callDef {D : DefTable} {Δ : AsmTable} {Γ Γ' Γb Γb' : Env} {m : String}
      {args : List Expr} {argTys : List Ty} {d : Defn} {ρ : Ty} :
      JudgeAll D Δ Γ args argTys Γ' → defGet? D m = some d →
      paramEnv d.params argTys = some Γb →
      Judge D (⟨m, argTys, ρ⟩ :: Δ) Γb d.body ρ Γb' →
      Judge D Δ Γ (.send none m args none) ρ Γ'
  /-- **Strictness for an explicit-receiver send**: if the receiver or any argument has
      type `.never`, the send itself has type `.never`.

      Sound for a reason that has nothing to do with the method being called: Ruby
      evaluates the receiver, then the arguments, then dispatches. If one of those
      evaluations does not return a value, dispatch never happens, so *no* claim about the
      result can be falsified. The rule deliberately does not mention `m` or consult
      `PrimSig` — it applies to a method this checker knows nothing about.

      Needed, not decorative: it is what lets `Validate.lean`'s first pass over `fact`'s
      body get past `n * fact(n-1)` with the recursive call at `.never`, and therefore what
      makes the base case of a recursion visible before the recursive case has a type.
      Without it there is no candidate to verify and `fun-recursive-factorial` is
      unreachable.

      Only the two send shapes get a strictness rule, because only they are needed. An
      `if` with a `.never` condition, an array literal with a `.never` element, and so on
      are all equally justified and equally absent; each would be a rule of its own, and
      none has a rung. -/
  | primNever {D : DefTable} {Δ : AsmTable} {Γ Γ₁ Γ₂ : Env} {recv : Expr}
      {m : String} {args : List Expr} {σ : Ty} {argTys : List Ty} :
      Judge D Δ Γ recv σ Γ₁ → JudgeAll D Δ Γ₁ args argTys Γ₂ →
      (σ = .never ∨ argTys.contains .never = true) →
      Judge D Δ Γ (.send (some recv) m args none) .never Γ₂
  /-- Strictness for an implicit-self call: the same argument as `primNever`, with no
      receiver to consider. Placed *before* `callAsm`/`callDef` in `Validate.lean`'s
      match, so a call with a non-returning argument is `.never` whether or not the method
      is defined — which is right: an undefined method is never reached either. -/
  | callNever {D : DefTable} {Δ : AsmTable} {Γ Γ' : Env} {m : String}
      {args : List Expr} {argTys : List Ty} :
      JudgeAll D Δ Γ args argTys Γ' → argTys.contains .never = true →
      Judge D Δ Γ (.send none m args none) .never Γ'
  /-- An explicit-receiver, block-less `send` whose receiver and arguments type, and
      whose resulting shape has a justified `PrimSig`.

      Three restrictions are each doing work: `some recv` (an implicit-self send has
      nobody to dispatch on in this fragment), `blk = none` (a block would need
      `Expr.block` typing, tier ≥ 9), and `PrimSig` matching the *synthesized* argument
      types exactly (no subsumption — see the module docstring). -/
  | prim {D : DefTable} {Δ : AsmTable} {Γ Γ₁ Γ₂ : Env} {recv : Expr} {m : String} {args : List Expr}
      {σ τ : Ty} {argTys : List Ty} :
      Judge D Δ Γ recv σ Γ₁ → JudgeAll D Δ Γ₁ args argTys Γ₂ → PrimSig σ m argTys τ →
      Judge D Δ Γ (.send (some recv) m args none) τ Γ₂

/-- Pointwise `Judge` over an argument list, with matching length by construction and
the environment threaded left to right (Ruby's argument evaluation order). -/
inductive JudgeAll : DefTable → AsmTable → Env → List Expr → List Ty → Env → Prop
  | nil {D : DefTable} {Δ : AsmTable} {Γ : Env} : JudgeAll D Δ Γ [] [] Γ
  | cons {D : DefTable} {Δ : AsmTable} {Γ Γ₁ Γ₂ : Env} {e : Expr} {es : List Expr} {τ : Ty} {τs : List Ty} :
      Judge D Δ Γ e τ Γ₁ → JudgeAll D Δ Γ₁ es τs Γ₂ → JudgeAll D Δ Γ (e :: es) (τ :: τs) Γ₂

/-- Key-then-value `Judge` over a hash literal's pairs, threading the environment in
Ruby's evaluation order. No types appear in the conclusion: this relation exists purely
to require that each key and each value *has* one (see `Judge.hashLit`). -/
inductive JudgePairs : DefTable → AsmTable → Env → List (Expr × Expr) → Env → Prop
  | nil {D : DefTable} {Δ : AsmTable} {Γ : Env} : JudgePairs D Δ Γ [] Γ
  | cons {D : DefTable} {Δ : AsmTable} {Γ Γ₁ Γ₂ Γ₃ : Env} {k v : Expr} {ps : List (Expr × Expr)} {κ ν : Ty} :
      Judge D Δ Γ k κ Γ₁ → Judge D Δ Γ₁ v ν Γ₂ → JudgePairs D Δ Γ₂ ps Γ₃ →
      JudgePairs D Δ Γ ((k, v) :: ps) Γ₃

/-- A non-empty statement sequence. The result type is the last statement's; every
earlier statement must still type (a statement nobody reads can still be type-stuck),
and each one's outgoing environment is the next one's incoming.

**Also where `D` grows.** `cons` continues with `extendDefs D e`, so a top-level `def`
becomes visible to the statements that follow it and to no earlier one. This is the only
rule in the file that changes `D`, and it is why `foo(); def foo; end` has no
derivation. -/
inductive JudgeSeq : DefTable → AsmTable → Env → List Expr → Ty → Env → Prop
  | last {D : DefTable} {Δ : AsmTable} {Γ Γ' : Env} {e : Expr} {τ : Ty} : Judge D Δ Γ e τ Γ' → JudgeSeq D Δ Γ [e] τ Γ'
  | cons {D : DefTable} {Δ : AsmTable} {Γ Γ₁ Γ₂ : Env} {e e' : Expr}
      {es : List Expr} {σ τ : Ty} :
      Judge D Δ Γ e σ Γ₁ → JudgeSeq (extendDefs D e) Δ Γ₁ (e' :: es) τ Γ₂ →
      JudgeSeq D Δ Γ (e :: e' :: es) τ Γ₂

end

end Ratchet
