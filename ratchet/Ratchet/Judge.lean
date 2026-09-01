import Ratchet.Expr
import Ratchet.Ty

/-!
# `Judge` — the hand-authored typing judgment

The **specification** half of the checker. `Ratchet/Validate.lean`'s `chk` is a
decision procedure; this file says *what it is deciding*. The split matters for the
ratchet: a rung is only honestly "climbed" when there is a derivation
`Judge Γ p τ Γ'` one can read and check by eye, not merely a `Bool` that came out
`true`.

## Scope: tiers 1–7's object model, and no more

Deliberately authored for the rungs reached so far (tier 1's eight literals, tier 2's
`send`-shaped rungs, tier 3's `var`/`vasgn`/`seq`/bare-`vcall`, tier 4's conditionals,
tier 5's array and hash literals and their `#[]`, tier 6's top-level `def` and
implicit-self calls, and tier 7's classes, `new`, instance variables, instance-method
dispatch and `self`), and nothing else. Consequences, each a real limitation to lift later,
not an oversight:

- **Two things thread, and both are flat.** `Judge κ Γ I e τ Γ' I'` reads: *in context `κ`,
  with locals `Γ` and instance variables `I`, `e` synthesizes `τ` and leaves `Γ'` and `I'`
  behind*. The output states are what make `x = 1; x = true; x` typeable — an assignment is
  an expression whose effect the next expression sees. Locals are a *flat*
  `List (String × Ty)` with `envSet` overwriting in place: real Ruby locals are not
  single-typed, so re-binding a name at a different type is correct behaviour, not a gap
  (rung `reassign-different-type`). Instance variables are a `Ty` spine rather than an
  `Env`, because they also have to sit inside `Ty.inst` — see there.
- **Locals and `@ivar`s only.** Rules mention `VarKind.lvar`/`.ivar` explicitly;
  `@@cvar`/`$gvar` have no rule, so a program touching one is simply not typed.
- **No `subTy` anywhere.** Every rule below matches types by construction. `subTy`
  exists in `Ratchet/Ty.lean` and is unused here on purpose: nothing yet has a subtype
  worth exploiting, and a subsumption rule admitted "for later" is a rule whose soundness
  nobody has had to justify against a rung. Tier 7's second clink — inheritance — is where
  that stops being true.
- **No inheritance, no `super`, no singleton methods.** `Cls.super?` is *recorded* by
  `extendClasses` and read by nothing: method lookup is `defGet? c.methods`, one class deep.
  So `class Dog < Animal` declares fine and `Dog.new` finds no `initialize`.
- **Callable values, but not blocks-to-builtins.** Tier 9's `lambda`/`proc` and `#call`
  are typed; a block *passed to* a method (`[1,2].map { … }`), `yield`, `&`-block parameters
  and block-locals are not. Tier 10's metaprogramming is untouched. Modules are typed (tier
  8), but only their
  singleton methods are reachable: `include`, `extend` and `module_function` have no rule, so
  a module's *instance* methods are recorded and unusable.
- **`self` is typed only inside an instance-method body**, and only as `.inst n Iself`.
  At top level `κ.selfTy` is `none`, which two rules depend on: `bareName` (which requires
  it) and `prim`'s "explicit receiver only" restriction (an implicit-self send at top level
  goes to the `defs` table). Inside `initialize` it is deliberately *also* `none` — see
  `newInst` for why that is a soundness requirement and not an omission.

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

/-- The receivers for which `nil?` is **the builtin `nil?`** — `Object#nil?` (always
`false`) or `NilClass#nil?` (always `true`). Tier 12's counterpart to `EqSafe`, and it
exists for the same reason: `nil?` is total on every object in the standard library, so
the honest row is a wildcard receiver — but a *wildcard* is exactly what this ladder has
twice declined to admit (clink 1 for `!`), because a wildcard receiver in this type
language also covers `.inst n ivars`, an instance of a class the **program** declared. A
program is free to write `def nil?; 1 + "a"; end`, and then a wildcard `nil?` row launders
a `TypeError`.

So the row is guarded, and the guard is "no user code can be reached through this type":
every constructor below denotes a builtin object whose `nil?` this ladder has checked
against the semantics. `.nilable τ` is admitted *only when `τ` is*, which is what makes
`nilable (inst Dog)` — a real type this checker produces, from indexing an
`arrayOf (inst Dog)` — stay out.

Deliberately absent, like `EqSafe`'s: `.any` (unfalsifiable), `.union` (no rung; the
recursive row would be easy and is not justified by anything yet), `.inst`/`.clsOf` (the
whole point of the guard), and `.clos` (a `Proc` does respond to `nil?`, but no rung asks
and every unnecessary row is one more claim to check). -/
inductive NilQSafe : Ty → Prop
  | int : NilQSafe .int
  | float : NilQSafe .float
  | bool : NilQSafe .bool
  /-- `nil.nil?` is `true`; the one receiver where the answer is not `false`. -/
  | nilT : NilQSafe .nilT
  | sym : NilQSafe .sym
  | cls {n : String} : NilQSafe (.cls n)
  | arrayOf {τ : Ty} : NilQSafe (.arrayOf τ)
  /-- `nilable τ` inherits the guard from `τ`: the value is either `nil` (safe by
      `nilT`) or a `τ`, so the row is justified exactly when `τ`'s is. -/
  | nilable {τ : Ty} : NilQSafe τ → NilQSafe (.nilable τ)

/-- **Every method `Object` gives every object**, as a relation (tier 10).

`method_missing` fires only when dispatch finds *nothing*, and "nothing" includes everything
inherited from `Object`: `Ghost.new.to_s` runs `Object#to_s`, not `method_missing`. This
judgment's class table holds only what the program declared, so without this list
`Judge.callMissing` would route `to_s`, `inspect`, `==`, `hash`, `class` — every one of them —
to `method_missing` and give it the *wrong type*.

**This is the one table on the ladder that has to be *complete* to be sound**, and the
direction is worth being explicit about: every other table here is a list of things the checker
is willing to claim, so a missing row costs a rung. This one is a list of things the checker must
**refuse** to claim, so a missing row is an unsoundness. It is generated from
`Object.new.methods` under CRuby 4.0.5 (51 public names), plus `initialize`/`initialize_copy`/
`initialize_clone`/`initialize_dup`/`method_missing`/`respond_to_missing?`, which are private or
protected and so not in that list but are still defined on `Object` and still reached before
`method_missing`.

Regenerate with `ruby -e 'puts Object.new.methods.map(&:to_s).sort.inspect'` if the Ruby version
this project targets changes. A name added to `Object` by a future Ruby and *not* added here is
the failure mode; a name here that Ruby drops merely costs a rung. -/
def objectMethodNames : List String :=
  ["!", "!=", "!~", "<=>", "==", "===", "__id__", "__send__", "class", "clone",
   "define_singleton_method", "display", "dup", "enum_for", "eql?", "equal?",
   "extend", "freeze", "frozen?", "hash", "initialize", "initialize_clone",
   "initialize_copy", "initialize_dup", "inspect", "instance_eval", "instance_exec",
   "instance_of?", "instance_variable_defined?", "instance_variable_get",
   "instance_variable_set", "instance_variables", "is_a?", "itself", "kind_of?",
   "method", "method_missing", "methods", "nil?", "object_id", "private_methods",
   "protected_methods", "public_method", "public_methods", "public_send",
   "remove_instance_variable", "respond_to?", "respond_to_missing?", "send",
   "singleton_class", "singleton_method", "singleton_methods", "tap", "then",
   "to_enum", "to_s", "yield_self"]

/-- The relation, one constructor over the list above, so that a `Judge` premise reads as a
proposition and `objectMethod?` discharges it by `decide`. -/
inductive ObjectMethod : String → Prop
  | mk {m : String} : objectMethodNames.contains m = true → ObjectMethod m

/-- The form `Judge.callMissing`'s fourth premise is discharged in: a derivation writes
`not_objectMethod rfl`, and the `rfl` is the kernel checking the name against the list. -/
theorem not_objectMethod {m : String} (h : objectMethodNames.contains m = false) :
    ¬ ObjectMethod m := by
  intro hc
  cases hc with
  | mk hin => exact absurd (h ▸ hin) (by simp)

/-- **The builtin class names this judgment will type as a constant** (tier 12).

One row per name, and each row is a claim of exactly one thing: evaluating this bare
constant at top level yields the class object of that name, without raising. That is true
for these because they are defined in every Ruby and this judgment has no rule for constant
*assignment*, so nothing in a typed program can rebind them.

Kept to the names `builtinAncestors` can answer `is_a?` for, plus `TrueClass`/`FalseClass`
(where the answer is `none` — `Ty.bool` covers both — so `is_a?(TrueClass)` types and
narrows nothing, which is the honest behaviour rather than a missing rule). Not here:
`Numeric`, `Comparable`, `Enumerable`, `Object` — all perfectly real, all appearing *inside*
`builtinAncestors`, and none needed as a `Ty` yet; adding one is a one-line row when a rung
writes it. -/
inductive BuiltinCls : String → Prop
  | integer : BuiltinCls "Integer"
  | float : BuiltinCls "Float"
  | string : BuiltinCls "String"
  | symbol : BuiltinCls "Symbol"
  | nilClass : BuiltinCls "NilClass"
  | trueClass : BuiltinCls "TrueClass"
  | falseClass : BuiltinCls "FalseClass"
  | array : BuiltinCls "Array"
  | hash : BuiltinCls "Hash"

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
  /-- `Symbol#to_s () → String` (tier 10's `metaprog-method-missing-fixed-arity`). Total, and
      needed because `method_missing` receives the missing name as a **Symbol**, so the
      idiomatic body immediately calls `to_s` on it. -/
  | symToS : PrimSig .sym "to_s" [] (.cls "String")
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
  -- ### Tier 12's row
  /-- `recv.nil? () → Bool` for a `NilQSafe` receiver (rung `narrow-nilable-nil-check`).

      Total and never coercing: `Object#nil?` returns `false` for every object,
      `NilClass#nil?` returns `true`, and neither takes an argument or can raise. The
      entire content of this row is therefore in `NilQSafe`, which says which receivers
      this ladder is willing to claim reach one of those two definitions rather than a
      user-written override. -/
  | nilQuery {σ : Ty} : NilQSafe σ → PrimSig σ "nil?" [] .bool

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

/-! ## Tier 7's class table, and the context bundle

A class is a *third* kind of thing the checker has to remember, and unlike a `def` it
carries two method tables and a superclass. At that point `Judge`'s index list stops being
readable, so the four **input-only** components — classes, methods, assumptions and the type
of `self` — are bundled into one `Ctx`. Nothing about the bundling is semantic; it is the
difference between five indices and one.

What is *not* in `Ctx` is what threads: the local environment and (new at tier 7) the ivar
spine. Those stay explicit, before and after, because reading a rule means reading how they
flow. -/

/-- One class declaration, as the checker sees it: a name, an optional superclass name, and
its two method tables. No types, and no ivar list — Ruby declares neither.

`smethods` are the **singleton** methods (`def self.origin`), which are a genuinely separate
namespace: `Point.origin` and a `Point`'s `origin` are different methods, and only the first
exists here. -/
structure Cls where
  name : String
  super? : Option String
  methods : List Defn
  smethods : List Defn
  /-- `true` for a `module`. One `Cls` serves both because everything tier 8 asks for —
      `M.foo` resolving to a `def self.foo` — is `callSMethod` unchanged, and duplicating the
      structure to express that would duplicate the lookups too.

      What the flag is *for* is the one place the two really differ: **a module cannot be
      allocated.** `M.new` raises `NoMethodError`, so `ctorGet?`/`instClsGet?` refuse a module
      and `newInst`/`newInstNoInit`/`selfNew` go through them. Without the flag, `M.new`
      would find no `initialize`, take the zero-argument allocator route, and certify a
      program that raises.

      A module's *instance* methods (a plain `def` in its body) are recorded in `methods` and
      are unreachable, which is correct-by-accident and worth saying out loud: they become
      callable through `include`/`extend`/`module_function`, none of which has a rule, so no
      program that uses one types at all. `M.foo` for an instance-method `foo` looks in
      `smethods`, misses, and is rejected — which is what Ruby does too. Tier 10's
      `include`/`extend` are what make them reachable, via the two fields below. -/
  isModule : Bool
  /-- Modules mixed into **instance** dispatch by `include M` in this class's body, in source
      order. `mroGet?` searches them after the class's own methods and before its superclass,
      and it searches them **reversed**, because a later `include` wins in Ruby. -/
  includes : List String
  /-- Modules mixed in **ahead of the class itself** by `prepend M` (tier 10). The only mixin
      direction that changes the *order* rather than just adding to it: `class C; prepend M;
      def f; …; end; end` gives `C.ancestors = [M, C, …]`, so `M#f` wins over `C#f` and a
      `super` inside `M#f` runs `C#f`. That second half is why prepend forced the MRO to become
      a **list** (`mroList?`) instead of a `super?` walk — `M`'s "next" is `C`, which is not
      `M`'s superclass and could not be found from `M` alone. -/
  prepends : List String
  /-- Modules mixed into **singleton** dispatch by `extend M`. The asymmetry with `includes` is
      the whole content of `extend`: it takes the module's *instance* methods (a plain `def M`)
      and makes them methods of the class **object**, so `smroGet?` looks in `.methods`, not in
      `.smethods`. `metaprog-extend`'s `module Loud; def shout; …; end; class Person; extend
      Loud; end; Person.shout` is exactly that one-line fact. -/
  extended : List String

abbrev CTable := List Cls

def clsGet? (C : CTable) (n : String) : Option Cls := C.find? (·.name == n)

/-- One member of a class body that this checker can read. -/
inductive ClsMember where
  | inst (d : Defn)
  | sing (d : Defn)
  /-- `include M` (tier 10). -/
  | incl (n : String)
  /-- `extend M` (tier 10). -/
  | ext (n : String)
  /-- `prepend M` (tier 10). -/
  | prep (n : String)

def clsMember? : Expr → Option ClsMember
  | .def' n ps b => some (.inst ⟨n, ps, b⟩)
  -- `def self.m` is the only `defs` receiver read: `def obj.m` for some other object is a
  -- singleton method on *that* object, which this checker has no way to record.
  | .defs .self' n ps b => some (.sing ⟨n, ps, b⟩)
  -- Tier 10. Both are ordinary implicit-self sends in the desugared syntax, and the argument
  -- is required to be a **bare constant**: `include some_expr` is not read, so the class does
  -- not enter the table and nothing using it is typed. That the named module is really a
  -- *module* is checked separately, by `Judge.classStmt` -- `include SomeClass` raises
  -- `TypeError` in Ruby, and the table cannot see `isModule` from here.
  | .send none "include" [.const n] none => some (.incl n)
  | .send none "extend" [.const n] none => some (.ext n)
  | .send none "prepend" [.const n] none => some (.prep n)
  | _ => none

def splitMembers :
    List ClsMember → List Defn × List Defn × List String × List String × List String
  | [] => ([], [], [], [], [])
  | .inst d :: ms => let (i, s, c, e, p) := splitMembers ms; (d :: i, s, c, e, p)
  | .sing d :: ms => let (i, s, c, e, p) := splitMembers ms; (i, d :: s, c, e, p)
  | .incl n :: ms => let (i, s, c, e, p) := splitMembers ms; (i, s, n :: c, e, p)
  | .ext n :: ms => let (i, s, c, e, p) := splitMembers ms; (i, s, c, n :: e, p)
  | .prep n :: ms => let (i, s, c, e, p) := splitMembers ms; (i, s, c, e, n :: p)

/-- A class body's instance and singleton methods, or `none` if the body contains anything
this checker cannot read.

**That `none` is doing two jobs at once**, which is why the restriction sits in one place.
It is what makes the body safe to *evaluate* unchecked — a `def`/`defs` statement never runs
its body, and `nil` is `nil`, so a body made only of those cannot be type-stuck — and it is
what makes the class readable into `CTable`. A body with an ivar assignment at class level, a
nested class, or anything executable is not typed at all: conservative in the direction that
costs rungs rather than soundness, and it is the shape every tier-7 rung has. -/
def classMethods? :
    Expr → Option (List Defn × List Defn × List String × List String × List String)
  | .nil => some ([], [], [], [], [])
  | .seq es => (es.mapM clsMember?).map splitMembers
  | e => (clsMember? e).map (fun m => splitMembers [m])

/-- **Every name mixed in by this class body is a declared `module`.**

`Judge.classStmt`'s guard, and a soundness requirement rather than tidiness: `include` and
`extend` raise `TypeError` on anything that is not a `Module` (`include String` →
"wrong argument type Class (expected Module)"), and `TypeError` is inside the family. Without
this premise, `class P; include SomeClass; end; P.new.a_method_of_SomeClass` would dispatch
happily and certify a program that raises before it ever gets there.

A name the table does not know at all is also refused. That is stricter than Ruby, which is
happy to `include` a module declared in another file — but this judgment has no notion of
another file, and a name it cannot resolve is a name whose `isModule` it cannot check. -/
def allModules (C : CTable) (ns : List String) : Bool :=
  ns.all (fun n => match clsGet? C n with
    | some c => c.isModule
    | none => false)

/-! ### Method lookup, up the chain

`defGet?` finds a method declared *on* a class. `mroGet?` finds the one dispatch would
actually run, walking `super?`, and returns **which class it was found in** as well as the
method — because `super` needs the definition site, not the receiver's class (see
`Judge.superCall`). -/

/-- Look `m` up in each of these modules' **instance** methods, in order, and report which
module it was found in.

One function for both mixin directions, because both consult `.methods`: `include` makes a
module's instance methods instance methods of the class, and `extend` makes them methods of
the class *object*. Only the table consulted at the call site differs. -/
def mixinGet? (C : CTable) : List String → String → Option (String × Defn)
  | [], _ => none
  | mn :: ms, m =>
    match clsGet? C mn with
    | some c =>
      match defGet? c.methods m with
      | some d => some (mn, d)
      | none => mixinGet? C ms m
    | none => mixinGet? C ms m

/-- The bounded walk, **singleton dispatch only** (tier 10). `k` is a depth budget, not a
natural part of the algorithm: `CTable` is data, so nothing stops it describing a cycle
(`class A < B` and `class B < A` cannot both be declared in Ruby, but the table does not know
that). Exhausting the budget answers `none`, which — like `chk`'s fuel — can only cost
completeness.

Instance dispatch used to go through here too, with a `sing : Bool` switch; `prepend` moved it
to `mroList?`/`searchMro`, because a prepended module's "next" is the class itself and that
cannot be found by following `super?`. Singleton dispatch has no prepend form in this model, so
it kept the simpler walk. -/
def lookupUpS (C : CTable) : Nat → String → String → Option (String × Defn)
  | 0, _, _ => none
  | k + 1, n, m =>
    match clsGet? C n with
    | none => none
    | some c =>
      match defGet? c.smethods m with
      | some d => some (n, d)
      | none =>
      -- `extend M` puts *M's instance methods* in the class object's table (`Cls.extended`),
      -- searched reversed so a later `extend` wins.
      match mixinGet? C c.extended.reverse m with
      | some hit => some hit
      | none =>
        match c.super? with
        | none => none
        | some sn => lookupUpS C k sn m

/-! ### The MRO as a list (tier 10)

`prepend` is what forced this. Up to tier 8 instance dispatch could be a walk over `super?`,
because "the next place to look" was always reachable from where you were. A prepended module
breaks that: in `class C; prepend M; end` the entry after `M` is `C`, and `C` is not `M`'s
superclass — nothing about `M` names it. So the ancestor **order** has to be built once, as a
list, and both dispatch and `super` become searches over it.

Ruby's order for one class is `prepends ++ [self] ++ includes`, most recent mixin first, then
the same for its superclass. `mroList?` builds exactly that. -/

/-- The full method-resolution order of `n`, most specific first, or `none` if the walk leaves
the table (the same refusal `ancestorsUp` makes, and for the same reason). -/
def mroListUp (C : CTable) : Nat → String → Option (List String)
  | 0, _ => none
  | k + 1, n =>
    match clsGet? C n with
    | none => none
    | some c =>
      let here := c.prepends.reverse ++ (n :: c.includes.reverse)
      match c.super? with
      | none => some here
      | some sn => (mroListUp C k sn).map (fun rest => here ++ rest)

def mroList? (C : CTable) (n : String) : Option (List String) :=
  mroListUp C C.length n

/-- The first entry of an MRO that defines `m`, and which entry it was. -/
def searchMro (C : CTable) : List String → String → Option (String × Defn)
  | [], _ => none
  | e :: es, m =>
    match clsGet? C e with
    | some c =>
      match defGet? c.methods m with
      | some d => some (e, d)
      | none => searchMro C es m
    | none => searchMro C es m

/-- Everything **after** `x` in a list, or `none` if `x` is not in it.

This is what `super` means, stated as a list operation: not "the superclass of where I was
declared" (which prepend makes wrong) but "keep going from where I was found". -/
def afterInMro : List String → String → Option (List String)
  | [], _ => none
  | e :: es, x => if e == x then some es else afterInMro es x

/-- Instance-method lookup: the first entry of `n`'s MRO that defines `m`, and where it was
found — because `super` needs the definition site, not the receiver's class (see
`Judge.superCall`). -/
def mroGet? (C : CTable) (n m : String) : Option (String × Defn) :=
  match mroList? C n with
  | some l => searchMro C l m
  | none => none

/-- Singleton-method lookup. Ruby inherits class methods down the chain too, so this is the
other walk over the other tables. -/
def smroGet? (C : CTable) (n m : String) : Option (String × Defn) :=
  lookupUpS C C.length n m

/-- `n` as something **allocatable**: the table entry, unless it is a module. See
`Cls.isModule` for why the refusal is a soundness requirement rather than tidiness. -/
def instClsGet? (C : CTable) (n : String) : Option Cls :=
  match clsGet? C n with
  | some c => if c.isModule then none else some c
  | none => none

/-- `n`'s constructor: `initialize`, found by the ordinary walk, but only for something that
can be allocated at all. Bundled into one lookup so the `newInst` rule's premise count did
not change when tier 8 added the module check. -/
def ctorGet? (C : CTable) (n : String) : Option (String × Defn) :=
  match instClsGet? C n with
  | some _ => mroGet? C n "initialize"
  | none => none

/-! ### The ancestor chain (tier 12)

`mroGet?` answers "which class would dispatch run this method from". `is_a?` asks a
different question — "is this class *among* those" — and needs the chain itself.

**Why the chain a declared class produces is complete**, which is the whole soundness
argument for answering `is_a?` **negatively**: a class enters `CTable` only via
`extendClasses`, which uses `classMethods?`, which is `mapM clsMember?` over the body — and
`clsMember?` reads only `def` and `def self.`. So a class body containing `include M`,
`extend M` or `prepend M` makes `classMethods?` answer `none`, the class never enters the
table, and `chk`'s `.class'` arm answers `none` for the whole program. Therefore *every*
class in this table has no mixins, and its real ancestors are exactly its declared chain
plus `Object`/`Kernel`/`BasicObject`.

That argument is load-bearing and fragile in a specific way: whichever tier gives
`include` a rule (tier 10) must revisit `isAAnswer`, because at that moment a class in the
table can have an ancestor the chain does not name. -/

/-- Names every object's chain ends with, and the reason `isANo` has to exclude them: `n`'s
declared chain stops at a class with no `super?`, whose real superclass is `Object`. -/
def rootAncestors : List String := ["Object", "Kernel", "BasicObject"]

/-- The ancestors contributed by a list of included modules — **one level only**, and `none`
if any of them mixes something in or has a superclass of its own.

That refusal is the soundness point (tier 10). `isAAnswer` answers `is_a?` *negatively* off
this chain, so an ancestor the chain fails to name is an unsoundness, not an imprecision. A
module that itself includes another module has an ancestor this function would omit, so instead
of omitting it the whole chain becomes unknown. Every rung includes only flat modules; making
this recursive is a fuelled walk nobody has needed. -/
def mixinAncestors? (C : CTable) : List String → Option (List String)
  | [] => some []
  | mn :: ms =>
    match clsGet? C mn with
    | none => none
    | some c =>
      if c.includes.isEmpty && c.super?.isNone then
        (mixinAncestors? C ms).map (fun rest => mn :: rest)
      else none

/-- The declared ancestor chain of `n`, most specific first, or `none` if the walk leaves the
table — an undeclared superclass means the chain is *unknown*, not empty, and answering
`is_a?` off a truncated chain would be unsound (`class Dog < StandardError` really is a
`StandardError`). Budgeted like `lookupUp`, for the same reason. -/
def ancestorsUp (C : CTable) : Nat → String → Option (List String)
  | 0, _ => none
  | k + 1, n =>
    match clsGet? C n with
    | none => none
    | some c =>
      -- Tier 10: a class's ancestors include the modules mixed into it. Omitting them would
      -- make `isAAnswer` answer `is_a?(SomeIncludedModule)` with a *wrong* `some false`.
      match mixinAncestors? C (c.prepends ++ c.includes) with
      | none => none
      | some _ =>
        -- The ancestor *set* is exactly the MRO's entries, and `mroListUp` already builds them
        -- in order -- so once the mixins are known to be flat, this walk and the MRO agree.
        -- Kept separate from `mroList?` only because a `none` here means "chain incomplete",
        -- which is a different claim from "dispatch found nothing".
        match c.super? with
        | none => some (c.prepends.reverse ++ (n :: c.includes.reverse))
        | some sn =>
          (ancestorsUp C k sn).map (fun rest =>
            (c.prepends.reverse ++ (n :: c.includes.reverse)) ++ rest)

def ancestors? (C : CTable) (n : String) : Option (List String) :=
  ancestorsUp C C.length n

/-- **The complete ancestor list of the class a builtin `Ty`'s values belong to**, most
specific first, modules included — checked against CRuby's `.ancestors`. Complete is the
operative word: this table is what lets `is_a?` be answered *negatively* for a builtin
receiver, so a missing entry would be an unsoundness rather than an imprecision.

`none` for every `Ty` whose values are not exactly one builtin class's instances:
`.bool` (`true` and `false` are instances of *two* classes, so `is_a?(TrueClass)` has no
single answer), `.union`/`.nilable` (handled compositionally by `isATy`/`notATy`), `.any`,
`.never`, `.inst` (a declared class — `ancestors?`'s job), `.clsOf`/`.clos` (`Class` and
`Proc`; total, but no rung asks and each row is a claim to check), and `.cls n` for any `n`
other than the two builtin classes this `Ty` actually produces. -/
def builtinAncestors : Ty → Option (List String)
  | .int => some (["Integer", "Numeric", "Comparable"] ++ rootAncestors)
  | .float => some (["Float", "Numeric", "Comparable"] ++ rootAncestors)
  | .nilT => some ("NilClass" :: rootAncestors)
  | .sym => some (["Symbol", "Comparable"] ++ rootAncestors)
  | .cls "String" => some (["String", "Comparable"] ++ rootAncestors)
  | .cls "Hash" => some (["Hash", "Enumerable"] ++ rootAncestors)
  | .arrayOf _ => some (["Array", "Enumerable"] ++ rootAncestors)
  | _ => none

/-- `is_a?(cn)` on a value of type `τ`: `some true` when **every** value of `τ` answers
`true`, `some false` when every value answers `false`, and `none` when this judgment cannot
tell — which is the answer for `.any`, `.bool`, a `.cls` outside `builtinAncestors`, and a
declared class whose chain leaves the table.

Not defined on `.union`/`.nilable`: those are not a single class, and treating them here
would hide the fact that a union's answer is per-member. `isATy`/`notATy` decompose them. -/
def isAAnswer (C : CTable) (cn : String) : Ty → Option Bool
  | .inst n _ => (ancestors? C n).map (fun ch => (ch ++ rootAncestors).contains cn)
  | τ => (builtinAncestors τ).map (fun ch => ch.contains cn)

/-- **`recv.is_a?(C)` really reaches `Object#is_a?`.**

`is_a?` is total on every object and never raises for a `Module` argument, so the only way
`x.is_a?(C)` can be type-stuck is a **user-written override** — and unlike `nil?` (see
`NilQSafe`, which sidesteps the problem by refusing `.inst` outright) `is_a?` *must* admit
`.inst`, because narrowing a union of program-declared classes is the whole point of
`narrow-union-subclass`.

So the guard is precise instead of structural: for every `.inst n` component of the receiver
type, `n`'s MRO must not define `is_a?`. That is a lookup this judgment already has, and it
is why this rule takes the class table where `PrimSig` rows cannot — which is also why
`is_a?` is a `Judge` rule rather than a `PrimSig` row.

`.any` is refused for `EqSafe`'s reason (a rule no rung can falsify), `.clos` because `Proc`
does respond to `is_a?` but no rung asks, and `.never` because the strictness rules
(`primNever`) get there first. -/
def isADispatchOk (C : CTable) : Ty → Bool
  | .inst n _ => (mroGet? C n "is_a?").isNone
  | .union σ τ => isADispatchOk C σ && isADispatchOk C τ
  | .nilable ρ => isADispatchOk C ρ
  | .any | .clos _ _ _ | .never | .sameAs _ _ => false
  | _ => true

/-- **Adding a class declaration to the table, merging if the name is already there.**

Tier 10's `metaprog-class-reopening`. Ruby lets a `class` statement *reopen* an existing
class, and the methods accumulate:

```ruby
class Foo; def a; 1; end; end
class Foo; def b; 2; end; end
Foo.new.a + Foo.new.b        # both work
```

This function used to prepend unconditionally, and `clsGet?` is a `find?`, so the second
statement **shadowed** the first: `Foo` had `b` and not `a`, and the program was untypeable.
Merging is the honest model, and note it is not a special case for "metaprogramming" — a
reopened class is the same thing a class always was, and the old behaviour was simply wrong
about it rather than conservative.

Three details, each a decision:

- **The later body's methods go first**, because `defGet?` is a `find?`: a redefinition must
  win over the definition it replaces, which is what Ruby does.
- **The superclass is the later one if it names one, else the earlier's.** `class Foo` with no
  `< Bar` does not erase an inherited superclass. (Ruby *rejects* a reopening that names a
  *different* superclass; this function would silently take the later, which no rung
  exercises.)
- **The merged entry is prepended rather than replacing the old one in place.** The stale entry
  is unreachable — `clsGet?` finds the new one first — and this keeps the function a one-liner
  instead of needing a list update. It does grow `C`, which only makes `mroGet?`/`ancestors?`'s
  `C.length` budget more generous. -/
def mergeCls (C : CTable) (c : Cls) : CTable :=
  match clsGet? C c.name with
  | none => c :: C
  | some old =>
    -- **Named fields, not positional.** `Cls` now has eight of them, three of which are
    -- `List String`, and a positional `⟨…⟩` silently swapped `includes` with `prepends` when
    -- tier 10 added the third -- which *validated* `metaprog-prepend` for the wrong reason
    -- (dispatch found `Person#speak` instead of `Logger#speak`, so the `zsuper` in the module
    -- was never reached). Named fields make that class of mistake a compile error.
    { name := c.name,
      super? := c.super?.orElse (fun _ => old.super?)
      methods := c.methods ++ old.methods
      smethods := c.smethods ++ old.smethods
      isModule := c.isModule
      -- Mixins accumulate the same way, and with the later body's *later* in the list, because
      -- every mixin list is searched reversed: a module mixed in by a reopening wins over one
      -- mixed in earlier.
      includes := old.includes ++ c.includes
      prepends := old.prepends ++ c.prepends
      extended := old.extended ++ c.extended } :: C

def extendClasses (C : CTable) : Expr → CTable
  | .class' n sup body =>
    match classMethods? body with
    | some (ms, sms, incs, exts, preps) =>
      match sup with
      | none =>
        mergeCls C
          { name := n, super? := none, methods := ms, smethods := sms, isModule := false
            includes := incs, prepends := preps, extended := exts }
      | some (.const sn) =>
        mergeCls C
          { name := n, super? := some sn, methods := ms, smethods := sms, isModule := false
            includes := incs, prepends := preps, extended := exts }
      -- A superclass expression that is not a bare constant (`class C < foo()`) is not
      -- read, so the class does not enter the table and nothing using it is typed.
      | some _ => C
    | none => C
  -- Tier 8. A module is a `Cls` with no superclass and the module flag set; the body is read
  -- by the same `classMethods?`, so `def self.foo` lands in `smethods` and `M.foo` is
  -- `callSMethod` with nothing added.
  | .module' n body =>
    match classMethods? body with
    | some (ms, sms, incs, exts, preps) =>
      mergeCls C
        { name := n, super? := none, methods := ms, smethods := sms, isModule := true
          includes := incs, prepends := preps, extended := exts }
    | none => C
  | _ => C

/-- Where the currently-executing method was **found** — which is not the same as the class
of the receiver, and `super` is the reason the distinction has to be recorded.

`Triangle#initialize` calls `super(3)`; the parent to delegate to is the superclass of
*`Triangle`*, the class the running method was declared in, and if that method had itself
been inherited from somewhere higher the answer would differ. `selfTy` names the receiver's
class and cannot answer this. The method name is here for the same reason: `super` calls the
method of the same name. -/
structure Frame where
  /-- The class of the object the running method is *running on* (tier 10). `super` needs it
      because a prepended module's "next" is the class that prepended it, and that is only
      findable in the **receiver's** MRO — `defClass` alone cannot name it.

      For a singleton method body this is the class object's own name, which is harmless: a
      `super` there would search instance methods and find nothing. -/
  recvClass : String
  /-- Where the running method was **found** — which for a prepended or included module is that
      module, not the receiver's class. `super` continues from just after it. -/
  defClass : String
  methName : String

/-! ## A structural `Expr` comparator that kernel-reduces

Tier 9 matches a block literal against the whole-program block table **by syntax**
(`closIdx?`), and `Expr`'s derived `BEq` cannot do that job: `Expr` is a *nested* inductive
(`List Expr`, `List (Expr × Expr)`), so the derived instance is compiled by well-founded
recursion and does not reduce in the kernel — which `Ratchet/Rungs.lean`'s per-rung `rfl`
checks and every `closIdx? … = some idx` premise depend on. This is the same fact that made
`Ty`'s arrow and ivar spines spines rather than list payloads; here it shows up on the other
side of the boundary, on syntax this package does not own.

So: hand-written, structurally recursive, with explicit list companions — exactly the shape
`collectBlocks` uses, which does reduce.

**The catch-all is `false`, and that is safe in both directions.** A constructor pair this
function does not cover compares unequal, so two syntactically *identical* blocks built from
uncovered syntax get no shared index — `closIdx?` misses, no rule applies, and the program is
not typed. Conservative. What is *not* possible is a spurious `true`: every covered case
compares every field. Coverage below is the constructors that appear in a block's parameters
or body anywhere in the corpus; the rest are honest omissions rather than a claim. -/

/-- Parameter comparison, **outside** the recursive group on purpose: `Param.opt` carries a
default `Expr`, and pulling `Expr` into this function's recursion would put it back in the
bundle. So an optional parameter compares `false` — conservatively, since a block with one
then has no index and is not typed, and no rung has one. -/
def paramEq : Param → Param → Bool
  | .req a, .req b => a == b
  | .rest a, .rest b => a == b
  | .kwrest a, .kwrest b => a == b
  | .block a, .block b => a == b
  | .fwd, .fwd => true
  | _, _ => false

def paramEqAll : List Param → List Param → Bool
  | [], [] => true
  | a :: as, b :: bs => paramEq a b && paramEqAll as bs
  | _, _ => false

mutual

def exprEq : Expr → Expr → Bool
  | .int a, .int b => a == b
  | .flt a, .flt b => a == b
  | .str a, .str b => a == b
  | .sym a, .sym b => a == b
  | .tru, .tru => true
  | .fls, .fls => true
  | .nil, .nil => true
  | .self', .self' => true
  | .var k a, .var k' b => k == k' && a == b
  | .vasgn k a e, .vasgn k' b e' => k == k' && a == b && exprEq e e'
  | .const a, .const b => a == b
  | .vcall a, .vcall b => a == b
  -- The `Option Expr` fields are matched inline rather than through a helper: an
  -- `Option Expr → Option Expr → Bool` companion is not part of the nested-inductive
  -- bundle Lean builds structural recursion from, and adding one is what pushes this whole
  -- group onto well-founded recursion — at which point it stops reducing in the kernel and
  -- every `rfl` that depends on it fails. Discovered the hard way; see
  -- `../implementation-notes.md` clink 9.
  | .send none m as none, .send none m' as' none =>
    m == m' && exprEqAll as as'
  | .send (some r) m as none, .send (some r') m' as' none =>
    exprEq r r' && m == m' && exprEqAll as as'
  | .send none m as (some b), .send none m' as' (some b') =>
    m == m' && exprEqAll as as' && exprEq b b'
  | .send (some r) m as (some b), .send (some r') m' as' (some b') =>
    exprEq r r' && m == m' && exprEqAll as as' && exprEq b b'
  | .block ps ls b, .block ps' ls' b' =>
    paramEqAll ps ps' && ls == ls' && exprEq b b'
  | .yield' as, .yield' as' => exprEqAll as as'
  | .blockpass none, .blockpass none => true
  | .blockpass (some e), .blockpass (some e') => exprEq e e'
  | .if' c t none, .if' c' t' none => exprEq c c' && exprEq t t'
  | .if' c t (some e), .if' c' t' (some e') =>
    exprEq c c' && exprEq t t' && exprEq e e'
  | .def' n ps b, .def' n' ps' b' => n == n' && paramEqAll ps ps' && exprEq b b'
  | .defs r n ps b, .defs r' n' ps' b' =>
    exprEq r r' && n == n' && paramEqAll ps ps' && exprEq b b'
  | .array es, .array es' => exprEqAll es es'
  | .hash ps, .hash ps' => exprEqPairs ps ps'
  | .ret none, .ret none => true
  | .ret (some e), .ret (some e') => exprEq e e'
  | .class' n none b, .class' n' none b' => n == n' && exprEq b b'
  | .class' n (some s) b, .class' n' (some s') b' =>
    n == n' && exprEq s s' && exprEq b b'
  | .module' n b, .module' n' b' => n == n' && exprEq b b'
  | .super' as none, .super' as' none => exprEqAll as as'
  | .super' as (some b), .super' as' (some b') => exprEqAll as as' && exprEq b b'
  | .seq es, .seq es' => exprEqAll es es'
  | _, _ => false

def exprEqAll : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => exprEq a b && exprEqAll as bs
  | _, _ => false

def exprEqPairs : List (Expr × Expr) → List (Expr × Expr) → Bool
  | [], [] => true
  | (k, v) :: ps, (k', v') :: ps' =>
    exprEq k k' && exprEq v v' && exprEqPairs ps ps'
  | _, _ => false

end

/-! ## Tier 9's block table

`Ty.clos` says why a callable's type is a *reference* rather than an arrow. This is what it
refers to. -/

/-- One block literal the program contains. `locals` (a `|x; y|` block-local list) is not
recorded because no rule admits a block that has any — see `Judge.lambdaLit`. -/
structure Clos where
  params : List Param
  body : Expr

abbrev ClosTable := List Clos

/-- The index of a block literal in the table, matched **by syntax**.

Syntax equality is `exprEq`, not `==`: the derived instance does not kernel-reduce (see
above). Syntactically identical blocks therefore share an index, and that is fine rather than
tolerated: an entry is only `(params, body)`, so two blocks that agree on both are
interchangeable *here*. What distinguishes two instances of the same block literal is the
environment each captured, and that lives in `Ty.clos`'s second argument, not in this
table. -/
def closIdxAux (k : Nat) : ClosTable → List Param → Expr → Option Nat
  | [], _, _ => none
  | c :: cs, ps, b =>
    if paramEqAll c.params ps && exprEq c.body b then some k
    else closIdxAux (k + 1) cs ps b

def closIdx? (K : ClosTable) (ps : List Param) (b : Expr) : Option Nat :=
  closIdxAux 0 K ps b

def closGet? (K : ClosTable) (k : Nat) : Option Clos := K[k]?

mutual

/-- Every block literal in the program, collected **before checking starts** so that
`Ctx.closures` is a constant and `Ty.clos`'s index means the same thing everywhere.

This is why tier 9 needed no fourth piece of threaded state: the alternative — allocating an
index when a lambda expression is reached — makes the table grow mid-expression, and then a
`Ty.clos k` would only be meaningful relative to a table that is still changing.

Coverage is the constructors that can contain a block in this corpus. **Anything unlisted
simply does not get its blocks registered**, so a lambda written there has no index, no rule
applies, and the program is not typed — conservative, and the failure is a rejection rather
than a wrong index. -/
def collectBlocks : Expr → ClosTable
  | .block ps _ body => ⟨ps, body⟩ :: collectBlocks body
  | .send recv _ args blk =>
    (match recv with | some r => collectBlocks r | none => []) ++
    collectBlocksAll args ++
    (match blk with | some b => collectBlocks b | none => [])
  | .seq es => collectBlocksAll es
  | .vasgn _ _ e => collectBlocks e
  | .def' _ _ body => collectBlocks body
  | .defs _ _ _ body => collectBlocks body
  | .class' _ _ body => collectBlocks body
  | .module' _ body => collectBlocks body
  | .array es => collectBlocksAll es
  | .hash ps => collectBlocksPairs ps
  | .if' c t e =>
    collectBlocks c ++ collectBlocks t ++
    (match e with | some x => collectBlocks x | none => [])
  | .yield' args => collectBlocksAll args
  | .blockpass (some e) => collectBlocks e
  | .super' args blk =>
    collectBlocksAll args ++ (match blk with | some b => collectBlocks b | none => [])
  | .ret (some e) => collectBlocks e
  | _ => []

def collectBlocksAll : List Expr → ClosTable
  | [] => []
  | e :: es => collectBlocks e ++ collectBlocksAll es

def collectBlocksPairs : List (Expr × Expr) → ClosTable
  | [] => []
  | (k, v) :: ps => collectBlocks k ++ collectBlocks v ++ collectBlocksPairs ps

end

/-- The read-only half of the judgment's state, bundled. `classes`/`defs` grow at statement
boundaries (`JudgeSeq.cons`), `asms` grows at a call site being discharged
(`Judge.callDef`), and `frame`/`selfTy` are set once, on entry to a method body, and never
threaded. -/
structure Ctx where
  classes : CTable
  defs : DefTable
  asms : AsmTable
  /-- The definition site of the running method, or `none` outside any method body. -/
  frame : Option Frame
  /-- Every block literal in the program, indexed by `Ty.clos`. Constant for a whole run —
      `validate` fills it in from `collectBlocks` and nothing changes it. -/
  closures : ClosTable
  /-- The **block** the currently-executing method was called with, as a `Ty.clos`, or `none`
      if it has none (or if we are not in a method body). This is what `yield` reads: Ruby
      passes a block implicitly, out of band from the argument list, and `yield` is the only
      way to reach it unless the method also names it with `&b`.

      Set by `callDefBlk` on entry to the body and by nothing else — in particular *not*
      inherited into a nested `callDef`, because a block does not propagate to methods the
      body calls. -/
  blockTy : Option Ty
  /-- The type of `self`, or `none` at top level.

      `none` rather than "the type of `main`" because this judgment has no rule that needs
      it: at top level, `self'` is not typed and an implicit-self send goes to the `defs`
      table. Inside a method body it is `some (.inst c ivars)`, which is what makes
      `class-self-returning-method` work — `self` there is not merely "a `Point`", it is
      *this* `Point`, ivars and all. -/
  selfTy : Option Ty

/-- The class name behind a `self` type, for `Frame.recvClass`. `.inst n _` and `.clsOf n`
are the only two shapes any body-entering rule supplies; anything else cannot arise and gets a
name no class has, which makes `super` fail rather than dispatch somewhere wrong. -/
def selfClsName : Ty → String
  | .inst n _ => n
  | .clsOf n => n
  | _ => ""

/-- Entering a method body whose `self` has type `σ`. Only `selfTy` changes: the class and
method tables are the ones in force at the call site, and the assumption table is *kept*,
because a recursive call made from inside a body must still find the assumption discharging
it. The body's *locals* are not in `Ctx` at all — they are the threaded `Env`, and a call
rule supplies `paramEnv`'s fresh one. -/
def Ctx.inMethod (κ : Ctx) (σ : Ty) (dc m : String) : Ctx :=
  { κ with selfTy := some σ, frame := some ⟨selfClsName σ, dc, m⟩ }

/-- Entering a body whose `self` this judgment declines to type — `initialize` (see
`Judge.newInst`) — but whose *definition site* still has to be recorded, because the body may
call `super`. -/
def Ctx.inCtor (κ : Ctx) (rc dc m : String) : Ctx :=
  { κ with frame := some ⟨rc, dc, m⟩ }

/-- `κ` after performing statement `e`: both syntax tables grow, nothing else changes. Used
only by `JudgeSeq.cons`, which is the only rule that knows about statement order. -/
def Ctx.afterStmt (κ : Ctx) (e : Expr) : Ctx :=
  { κ with classes := extendClasses κ.classes e, defs := extendDefs κ.defs e }

/-- `paramEnv` for a call that **carries a block**. Same walk, plus one case: a
`&b` parameter (`Param.block`) consumes not an argument but the block itself.

`blk` is `none` when the call passes no block, and then `&b` binds `.nilT` — which is exactly
Ruby (`def run(&b); b; end; run` is `nil`), and also exactly why the binding cannot be
skipped: `b` is in scope either way. A `&b` parameter is required to come **last**, which is
not enforced here because the parser already guarantees it. -/
def paramEnvB (blk : Option Ty) : List Param → List Ty → Option Env
  | [], [] => some []
  | .req x :: ps, τ :: τs => (paramEnvB blk ps τs).map (fun Γ => (x, τ) :: Γ)
  | .block (some x) :: ps, τs =>
    (paramEnvB blk ps τs).map (fun Γ => (x, blk.getD .nilT) :: Γ)
  | .block none :: ps, τs => paramEnvB blk ps τs
  | _, _ => none

/-! ## Tier 9c: the builtin iterators

The last piece of tier 9, and a genuinely new *kind* of rule: a builtin whose signature
mentions a **block**. `PrimSig` cannot state one — it relates a receiver type, a name and a
list of argument types to a result, and an iterator's result depends on what its *block*
returns, which is not known until the block's body has been typed.

So the signature is split in two, and the split is the design:

- **`iterParams?`** answers "given the receiver's element type and the call's arguments, at
  what types does the block's parameter list get bound?" — the information needed *before*
  typing the body.
- **`iterResult?`** answers "given that the body came back at `ρ`, what does the call
  return?" — after.

`IterSig` is the relation that joins them, with one constructor per iterator, and
`iterSig?_sound` is the lemma that the two functions only ever agree with it.

**The five iterators differ in exactly the way that matters**, which is why a single "block
rule" would get most of them wrong:

| method | block params | result |
|---|---|---|
| `each` | `[elem]` | the **receiver** |
| `map` | `[elem]` | `arrayOf` (block's return) |
| `select` | `[elem]` | `arrayOf elem` (a subset of the receiver) |
| `sort_by` | `[elem]` | `arrayOf elem`, **if** the block's return is comparable |
| `inject(init)` | `[α, elem]` | `α`, **if** the block returns `α` |

The two side conditions are not decoration:

- **`sort_by` needs `Comparable ρ`**, and the failure mode is not the obvious one. It is not
  that some key type lacks `<=>`: `nil <=> nil` is `0`, so `["a","b"].sort_by { |s| nil }`
  sorts fine. What raises is a key type whose `<=>` is not total **across its own values** —
  a union (`[1, "a"].sort_by { |x| x }` raises `ArgumentError: comparison of Integer with
  String failed`, *inside* the family) or a user class inheriting `Object#<=>`, which answers
  `0` for identical objects and `nil` otherwise (`[Z.new, Z.new].sort_by { |x| x }` raises).
  So an unconstrained `sort_by` row would be unsound, unlike `select`'s — a `select` block's
  result is only ever tested for truthiness, which never raises.
- **`inject`'s accumulator must be a fixed point.** `α` is the type of the initial value, the
  block is typed with its first parameter at `α`, and the body is *required to come back at
  `α`* — because the block's result is the next iteration's accumulator. A block that returns
  something else really does change the accumulator's type between iterations, and no single
  `Ty` describes it. This is the same assume-then-verify shape as `Judge.callDef`'s recursion,
  with the initial value playing the part of the candidate. -/

/-- Receivers of `<=>` for which `sort_by`'s comparison is total. One row per type this
`Ty` can actually produce a homogeneous array of; a `union` is deliberately absent, because
`[1, "a"].sort_by { |x| x }` really does raise `ArgumentError`. -/
inductive Comparable : Ty → Prop
  | int : Comparable .int
  | float : Comparable .float
  | str : Comparable (.cls "String")

/-- `IterSig m elem args βs ρ res`: sending `m` with argument types `args` and a block to an
`arrayOf elem` binds the block's parameters at `βs`; if the block's body then has type `ρ`,
the call's result is `res`. See the section docstring for the table and the two side
conditions. -/
inductive IterSig : String → Ty → List Ty → List Ty → Ty → Ty → Prop
  /-- `Array#each { |x| … } → self`. The block's return value is discarded entirely. -/
  | each {τ ρ : Ty} : IterSig "each" τ [] [τ] ρ (.arrayOf τ)
  /-- `Array#map { |x| … } → Array` of whatever the block returned. -/
  | map {τ ρ : Ty} : IterSig "map" τ [] [τ] ρ (.arrayOf ρ)
  /-- `Array#select { |x| … } → Array` of the *receiver's* elements. The block's result is
      only tested for truthiness, and truthiness never raises, so `ρ` is unconstrained. -/
  | select {τ ρ : Ty} : IterSig "select" τ [] [τ] ρ (.arrayOf τ)
  /-- `Array#sort_by { |x| … } → Array` of the receiver's elements, ordered by the block's
      results — which are compared with `<=>`, hence `Comparable`. -/
  | sortBy {τ ρ : Ty} : Comparable ρ → IterSig "sort_by" τ [] [τ] ρ (.arrayOf τ)
  /-- `Array#inject(init) { |acc, x| … } → α`, where `α` is `init`'s type and the block is
      required to *return* `α`. An empty receiver returns `init`, which is why the result is
      `α` rather than the block's return type — they are the same type by the premise. -/
  | inject {τ α : Ty} : IterSig "inject" τ [α] [α, τ] α α

/-! ### A closure's creation context (tier 11)

`Ty.clos`'s third field records the `self` of the closure's *creation* site. These two
functions decode it, and `Ctx.inClosure` is the context a body is judged in.

The point of the whole arrangement, stated once: **a closure body's `self` and instance
variables come from where the closure was made; its class/method tables come from where it is
called.** The first half is what these functions are for. The second half is deliberate and
correct: Ruby resolves a method call inside a block at *call* time, so a body that calls a
method defined after the block literal but before the invocation works, and carrying the call
site's tables is what models that. -/

/-- The `self` type a closure was created under, or `none` for one created where `self` was
not typed (top level), which `Ty.clos` encodes as `.never`. -/
def closSelf? (σ : Ty) : Option Ty := if σ == .never then none else some σ

/-- The ivar spine a closure's body must be judged against: the instance variables of the
object that was `self` when it was created.

`.ivar0` for anything that is not an `.inst`, which covers both the top-level case (`.never`)
and a closure created inside a singleton method (`.clsOf n`, whose `self` is a class object
with no ivars this checker models). Relies on an invariant every body-entering rule maintains:
where `κ.selfTy = some (.inst n I)`, the threaded spine *is* `I` (`Judge.callMethod`,
`Judge.selfCall`). -/
def closSpine (σ : Ty) : Ty :=
  match σ with
  | .inst _ ivars => ivars
  | _ => .ivar0

/-- The context a closure's body is judged in: the recorded `self`, and **no frame and no
block**.

Both erasures are conservative rather than principled, and each is recorded as such: a
`super` inside a closure body has no rule (`frame = none`), and a `yield` inside a closure
body has no rule (`blockTy = none`) even though Ruby resolves it to the enclosing method's
block. Making either precise means recording it in `Ty.clos` too, exactly as `selfTy` now is;
no rung asks. -/
def Ctx.inClosure (κ : Ctx) (σ : Ty) : Ctx :=
  { κ with selfTy := closSelf? σ, frame := none, blockTy := none }

/-- The block-local list of a `|x; y|` block (the desugarer's third `block` field), bound at
`.nilT`.

`.nilT` and not "unbound" because that is what Ruby does: a block-local is *declared* by the
`; y`, and reading it before assigning yields `nil` — the same fact `ivarGet?`'s defaulting
records one state over. Every rung that has one assigns before reading, so the value is never
observed; binding it anyway is what makes the name in scope at all. -/
def blockLocals : List String → Env
  | [] => []
  | x :: xs => (x, .nilT) :: blockLocals xs

/-- **Every name a closure captured still has the type it had on entry to its body.**

The premise that stops a block from retyping a captured local out from under its caller —
`callMethod`'s no-retyping premise, for locals instead of instance variables. The two are the
same rule stated twice, and the general form is worth naming: *a callee may not retype state
its caller can still see.*

Why it is needed, concretely (this was a real bug, found by fuzzing a class-plus-block program
and fixed in clink 11):

```ruby
def t; yield(1); end
a = 1
t { |x| a = "s" }
a + 1                 # TypeError
```

A Ruby block captures locals **by reference**, but `Ty.clos` captures by *value* into a spine
and the call rules discard the body's outgoing environment. So without this premise the caller
still believes `a : Int` after the block ran, and `a + 1` certifies a program that raises.

`Γin` is the body's incoming environment (`paramEnv … ++ spineToEnv cap`), not the spine
itself, so a captured name **shadowed by a block parameter** is compared at the parameter's
slot. That is stricter than necessary — assigning to a shadowing parameter cannot affect the
outer variable — and rejects `a = 1; lambda { |a| a = 2 }.call(3)`. Conservative, no rung
shadows, and recorded here rather than fixed because the precise version needs the premise to
know which names `paramEnv` bound.

What it costs in general: a block that accumulates into an outer local at a *different* type
is rejected. A block that accumulates at the *same* type (`a = a + x`) is fine — the value
changes, the type does not — which is the common case and the same boundary
`class-setter-method` sits on for ivars. The precise alternative is to thread the body's
outgoing environment back out and join it with the caller's (a block may run zero times, so a
join is required, and for `each` it would need a fixpoint). Not built; no rung needs it. -/
def capIntact : Ty → Env → Env → Bool
  | .ivarCons x _ rest, Γin, Γout =>
    (envGet? Γout x == envGet? Γin x) && capIntact rest Γin Γout
  | _, _, _ => true

/-- The expression whose type is a body's **result**.

For almost every body that is the body itself. The one case that differs is a body which is
exactly `return e`: calling it evaluates `e` and returns it, so the result type is `e`'s —
whereas `.ret` has no rule of its own and the body would otherwise be untypeable
(`lambda-explicit-return`).

**Why this is a function on the body rather than a `Judge` rule for `.ret`.** The obvious rule
— `.ret e` synthesizes `e`'s type — is *unsound*: it makes `def f; return "a"; 2; end`
validate at `Int`, because `JudgeSeq` takes the last statement's type and the `return` never
lets the last statement run. Typing `.ret e` as `.never` does not help for the same reason.
Matching the body's *whole shape* sidesteps it: a `return` anywhere other than as the entire
body still has no rule, so `seq [return "a", 2]` remains underivable. The general fix — a
judgment that accumulates return types across a body — is a real design and no rung needs
it. Applied only at `closCall`, because only a lambda rung asks; a *method* whose body is
exactly `return e` is still not typed. -/
def bodyResult : Expr → Expr
  | .ret (some e) => e
  | e => e

/-! ## Tier 12's narrowing

The capability that makes `nilable` and `union` usable: inside a branch of an `if`, a local
that the *condition tested* has a smaller type than it did outside.

Three pieces, deliberately separated:

1. **`NarrowKind`** — *which* runtime test the condition performs. One constructor per
   test, not one per condition shape, because several syntactic forms can perform the same
   test.
2. **`NarrowCond`** — the syntactic recognizer, as a relation: `NarrowCond c x k` says the
   condition `c` tests local `x` by test `k`. This is the part that is *not* obvious and is
   the reason narrowing is a judgment premise rather than an environment rewrite; see the
   `Judge.if'` docstring.
3. **`narrowEnvs`** — the two branch environments, as a **total function**. Total, and the
   identity on every condition `narrowCond?` does not recognize, which is why folding
   narrowing into `Judge.if'` itself did not change a single earlier rung: no rung below
   tier 12 has a condition of a recognized shape.

What is deliberately *not* here (each is a later rung of tier 12, and each needs machinery
this does not have): `is_a?`/`===` narrowing (needs `subTy`, and `Integer` as a `.clsOf`
for a class the program did not declare), aliasing (`case v when Integer` tests a
*temporary* and the branch bodies use `v`), narrowing an ivar rather than a local, and
narrowing by a branch that `return`s. -/

/-- The runtime test a narrowing condition performs. -/
inductive NarrowKind where
  /-- Truthiness: the bare condition of an `if`. Then-branch gets `truthyTy`, else-branch
      `falsyTy`. -/
  | truthy
  /-- `x.nil?`. Then-branch gets `isNilTy`, else-branch `nonNilTy`. Note the polarity: the
      *then*-branch is the one where `x` **is** `nil`, which is the single most likely place
      to write a narrowing rule backwards — and `corpus/135-narrow-backwards-unsafe` exists
      to catch exactly that. -/
  | isNil
  /-- `x.is_a?(C)`, carrying the class name. The first kind whose refinement needs the class
      table, which is why the two `refine*` functions take one. -/
  | isA (name : String)
deriving DecidableEq, Repr

/-! ### The `is_a?` refinements

`truthyTy` and friends project out of a type by *shape*. These two project out by **class
membership**, which is a question about the program's class table, and they are the first
refinements that answer it.

Both work member-by-member over a union, and the `nilable` case is the same decomposition
with `nilT` as the implicit second member. A member the checker cannot decide
(`isAAnswer = none`) is **kept in both branches**, which is the conservative direction: the
refinement narrows nothing and the branch is typed at the same type it had. -/

/-- What a `nil` member contributes to the then-branch: `nil.is_a?(cn)` is decided by
`NilClass`'s chain, which `builtinAncestors .nilT` gives. -/
def isANilPart (cn : String) : Ty :=
  if ("NilClass" :: rootAncestors).contains cn then .nilT else .never

/-- …and to the else-branch, which is its complement. -/
def notANilPart (cn : String) : Ty :=
  if ("NilClass" :: rootAncestors).contains cn then .never else .nilT

/-- The values of `τ` that **are** a `cn`. -/
def isATy (C : CTable) (cn : String) : Ty → Ty
  | .union σ τ => joinT (isATy C cn σ) (isATy C cn τ)
  | .nilable ρ => joinT (isANilPart cn) (isATy C cn ρ)
  | τ => match isAAnswer C cn τ with
    | some false => .never
    | _ => τ

/-- The values of `τ` that are **not** a `cn`. -/
def notATy (C : CTable) (cn : String) : Ty → Ty
  | .union σ τ => joinT (notATy C cn σ) (notATy C cn τ)
  | .nilable ρ => joinT (notANilPart cn) (notATy C cn ρ)
  | τ => match isAAnswer C cn τ with
    | some true => .never
    | _ => τ

/-- The refinement the **then**-branch applies. -/
def refineThen (C : CTable) : NarrowKind → Ty → Ty
  | .truthy, τ => truthyTy τ
  | .isNil, τ => isNilTy τ
  | .isA cn, τ => isATy C cn τ

/-- The refinement the **else**-branch applies. -/
def refineElse (C : CTable) : NarrowKind → Ty → Ty
  | .truthy, τ => falsyTy τ
  | .isNil, τ => nonNilTy τ
  | .isA cn, τ => notATy C cn τ

/-- Which branches a recognized condition licenses a refinement in (tier 12's
`narrow-and-guard`).

`both` is every test up to now: the outcome of `x.nil?` says something definite in each branch.
`thenOnly` is what a **conjunction** licenses. `if x && x > 1` is truthy only if `x` was truthy,
so the then-branch learns that — but the else-branch could have been taken because the *other*
conjunct was false, and then nothing at all is known about `x`. Refining the else-branch there
would be the exact mistake `corpus/135-narrow-backwards-unsafe` exists to catch, one level up. -/
inductive NarrowSides where
  | both
  | thenOnly
deriving DecidableEq, Repr

mutual

/-- **This expression cannot assign to a local**, decided by whitelist.

Needed by the `&&` recognizer, and the reason is a real hole rather than caution. `if x && rhs`
refines `x` in the then-branch because a truthy condition means `x` was truthy — but the
condition's *value* is `rhs`'s, so `x && (x = false; 1)` is truthy while leaving `x` false. The
refinement is applied to the environment as of the **end** of the condition, so an `rhs` that
reassigns `x` would have it refined at its new type on the strength of a test on its old value.

A **whitelist**, so that anything this function has not been taught about answers `false`. The
alternative — walking the syntax looking for `vasgn` — is wrong in the dangerous direction: a
constructor the walk does not cover would be reported clean. Method calls are admitted because a
method body cannot see its caller's locals; block-carrying sends are not, because a block body
can. -/
def noLocalAsgn : Expr → Bool
  | .int _ | .flt _ | .str _ | .sym _ | .tru | .fls | .nil => true
  | .var _ _ => true
  | .const _ | .self' => true
  | .send recv _ args none =>
    (match recv with | some r => noLocalAsgn r | none => true) && noLocalAsgnAll args
  | .array es => noLocalAsgnAll es
  | .if' c t e =>
    noLocalAsgn c && noLocalAsgn t && (match e with | some x => noLocalAsgn x | none => true)
  | .seq es => noLocalAsgnAll es
  | _ => false

def noLocalAsgnAll : List Expr → Bool
  | [] => true
  | e :: es => noLocalAsgn e && noLocalAsgnAll es

end

/-- `NarrowCond c x k`: evaluating condition `c` performs test `k` on the local `x`, *and
evaluating it has no other effect that could invalidate the refinement*.

That second clause is why both constructors are so restrictive. A refinement is a claim
about the value of `x` **at the point the branch begins**, so the condition must be an
expression whose evaluation cannot rebind `x` in between. Both forms below are: reading a
local, and sending a total zero-argument builtin to a local. A condition like
`(x = f()) .nil?` would test the new `x` and be fine, but `foo(x.nil?)` would not, and the
general side condition ("the condition assigns to no local the refinement mentions") is a
premise this ladder has not needed to state because no recognized form can assign at
all. -/
inductive NarrowCond : Expr → VarKind → String → NarrowKind → NarrowSides → Prop
  /-- `if x` / `if @x` — the condition is exactly a variable read. Ruby tests the value's
      truthiness and nothing else, so the then-branch has it non-`nil`/non-`false` and the
      else-branch has it one of those two. -/
  | bareVar {k : VarKind} {x : String} : NarrowCond (.var k x) k x .truthy .both
  /-- `if x.nil?` — `nil?` is total (`PrimSig.nilQuery`) and answers exactly "is this
      value `nil`". The receiver being a bare variable read is what ties the answer to `x`. -/
  | nilQuery {k : VarKind} {x : String} :
      NarrowCond (.send (some (.var k x)) "nil?" [] none) k x .isNil .both
  /-- `if x.is_a?(C)`, with the class written as a **bare constant**. The class name is read
      off the *syntax* rather than off the argument's type, and the two agree because the
      only rules that type a `.const n` (`constCls`, `constBuiltin`) both answer
      `.clsOf n` for the very same `n`. A non-constant argument (`x.is_a?(k)`) is not
      recognized: the rule `Judge.isAQuery` would still type the send, but there would be no
      class *name* to refine by. -/
  | isAQuery {k : VarKind} {x cn : String} :
      NarrowCond (.send (some (.var k x)) "is_a?" [.const cn] none) k x (.isA cn) .both
  /-- `case x when C` — the desugarer emits `C === x`, the *receiver* being the class. Same
      refinement as `is_a?`, reached from the other side, because `Module#===` is the ancestor
      test with its arguments swapped. -/
  | caseEqQuery {k : VarKind} {x cn : String} :
      NarrowCond (.send (some (.const cn)) "===" [.var k x] none) k x (.isA cn) .both
  /-- **`x && rhs`** — Ruby's `&&` desugars to a temporary plus a nested `if`, so an entire
      `seq` sits in the outer condition's position:

      ```
      seq (vasgn local __dt_t1 (var local x))
          (if (var local __dt_t1) rhs (var local __dt_t1))
      ```

      Its value is `rhs`'s when `x` is truthy and `x`'s (falsy) otherwise, so **truthy implies
      `x` was truthy** — and that is all it implies, which is why the sides are `thenOnly`.

      `noLocalAsgn rhs` is the premise that makes even the then-branch sound: the refinement is
      applied to the environment at the *end* of the condition, and `x && (x = false; 1)` is
      truthy while leaving `x` false.

      Note the alias in the desugared form is doing work *inside* the condition too:
      `x > 1` needs `x` narrowed, and it gets that from the **inner** `if`, whose condition is
      the temporary (`Ty.sameAs`, clink 25). The refinement is consumed in the same expression
      that establishes it. -/
  | andGuard {k : VarKind} {t x : String} {rhs : Expr} :
      noLocalAsgn rhs = true →
      NarrowCond
        (.seq [.vasgn k t (.var k x), .if' (.var k t) rhs (some (.var k t))])
        k x .truthy .thenOnly

/-- The executable recognizer. `none` means "this condition tells the checker nothing",
which is the answer for every condition in tiers 1–11.

**The `VarKind` is part of the answer** (tier 12c), because a refinement lands in a different
piece of state depending on it: a `.lvar` narrows the environment (`narrowEnvs`), an `.ivar`
narrows the spine (`narrowSpine`), and `.cvar`/`.gvar` narrow nothing, because no rule in this
judgment types either — so both consumers below are the identity on them, which is the right
answer rather than an omission. -/
def narrowCond? : Expr → Option (VarKind × String × NarrowKind × NarrowSides)
  -- Tier 12's `&&`, matched first because its shape is a `seq` and nothing else here is.
  | .seq [.vasgn k t (.var k' x), .if' (.var k'' t') rhs (some (.var k''' t''))] =>
    if k == k' && k == k'' && k == k''' && t == t' && t == t'' && noLocalAsgn rhs then
      some (k, x, .truthy, .thenOnly)
    else none
  | .var k x => some (k, x, .truthy, .both)
  | .send (some (.var k x)) "nil?" [] none => some (k, x, .isNil, .both)
  | .send (some (.var k x)) "is_a?" [.const cn] none => some (k, x, .isA cn, .both)
  -- Tier 12: `C === x`, which is what `case x when C` desugars to (with `x` a temporary --
  -- see `Ty.sameAs`). `Module#===` is the ancestor test with the sides swapped, so it narrows
  -- exactly as `is_a?` does.
  | .send (some (.const cn)) "===" [.var k x] none => some (k, x, .isA cn, .both)
  | _ => none

/-- Refine one name, **and the name it aliases** (tier 12).

The second half is the whole point of `Ty.sameAs`: `case v when Integer` tests a temporary and
its branch bodies use `v`, so refining only the tested name refines the wrong one. The alias's
target is refined from **its own current binding**, not from the alias's payload — the two are
equal by construction, and reading the binding makes it obviously so rather than an invariant to
maintain. The alias itself is kept, with a refined payload, so a *second* test on the same
temporary (the `when String` arm, which sits in the first arm's else-branch) narrows again. -/
def refineOne (C : CTable) (k : NarrowKind) (thenSide : Bool) (Γ : Env) (x : String) : Env :=
  let refine := fun τ => if thenSide then refineThen C k τ else refineElse C k τ
  match envGet? Γ x with
  | none => Γ
  | some (.sameAs y τ) =>
    let Γ₁ := envSet Γ x (.sameAs y (refine τ))
    match envGet? Γ₁ y with
    | some ρ => envSet Γ₁ y (refine (stripAlias ρ))
    | none => Γ₁
  | some τ => envSet Γ x (refine τ)

/-- The names the desugarer introduces for its own temporaries, which is where `Judge.vasgnAlias`
admits an alias.

A **list of whole names, not a prefix test**, for a reason that is not about design: Lean's
`String.isPrefixOf` is compiled by well-founded recursion and its termination proof pulls in
`Classical.choice`, which would have shown up in `chk_sound`'s axiom list. Every other table in
this package is `List.contains`-shaped and choice-free, and this one is too.

The direction of error if the desugarer ever emits a name past the end of this list is
**conservative**: no alias is recorded, the rung that needed one is not typed, and the ratchet
reports it. Only `__dt_t1` appears in the current corpus; the list runs to nine so that a `case`
with several scrutinees does not silently stop working. -/
def desugarTemps : List String :=
  ["__dt_t1", "__dt_t2", "__dt_t3", "__dt_t4", "__dt_t5",
   "__dt_t6", "__dt_t7", "__dt_t8", "__dt_t9"]

/-- **The two branch environments of an `if`, given the state at the end of its condition.**

Total by construction, and the identity in three separate circumstances, each for its own
reason: the condition is not a recognized test; the tested name is not a local the
environment knows (so there is nothing to refine — a `vcall`-shaped bare name reaches
`narrowCond?` as a `.var .lvar` only when the desugarer saw an assignment, but the
environment lookup can still miss inside a method body whose `paramEnv` did not bind it);
or, implicitly, the refinement happens to be the type it already had.

Being total is what lets `Judge.if'` carry narrowing in its *own* premises rather than in
a second, parallel `ifNarrow` rule — and that in turn is what keeps there from being two
rules for one syntactic form, only one of which anybody reads. -/
def narrowEnvs (C : CTable) (c : Expr) (Γ : Env) : Env × Env :=
  match narrowCond? c with
  | some (.lvar, x, k, sides) =>
    (refineOne C k true Γ x,
     match sides with
     | .both => refineOne C k false Γ x
     | .thenOnly => Γ)
  | _ => (Γ, Γ)

/-- **The two branch ivar spines**, the same construction one piece of state over
(tier 12c, `narrow-union-in-ivar`).

Two differences from `narrowEnvs`, both consequences of what a spine is:

- **There is no "not found" case.** Reading an instance variable that was never assigned
  yields `nil` in Ruby, so a miss refines `.nilT` rather than declining to refine — which is
  the same `.getD .nilT` `Judge.ivarRead` uses, and it is *informative*: `if @v.is_a?(Integer)`
  on a never-assigned `@v` types the then-branch with `@v : never`, i.e. as unreachable, which
  is exactly right.
- **`ivarSet` appends**, so refining a name the spine does not carry lengthens it. Harmless:
  the added binding is what `ivarRead` would have defaulted to anyway, and `Judge.if'`'s
  outgoing spine is `joinSpine I₁ I₂`, which puts it back. -/
def narrowSpine (C : CTable) (c : Expr) (I : Ty) : Ty × Ty :=
  match narrowCond? c with
  | some (.ivar, x, k, sides) =>
    let τ := (ivarGet? I x).getD .nilT
    (ivarSet I x (refineThen C k τ),
     match sides with
     | .both => ivarSet I x (refineElse C k τ)
     | .thenOnly => I)
  | _ => (I, I)

mutual

/-- `Judge κ Γ I e τ Γ' I'`: in context `κ` (classes, methods, assumptions, the type of
`self`), with locals `Γ` and instance variables `I`, the expression `e` synthesizes type `τ`
and leaves locals `Γ'` and instance variables `I'`. Nothing is trusted — see the module
docstring, and `AsmTable` for what a non-empty `κ.asms` means.

Read each literal rule as an assertion about the real semantics: evaluating this literal
yields a value whose class is the one `τ` names. `CheckRungs.lean` checks precisely that,
by running the actual `stepFn`.

**Two things thread, in evaluation order.** `Γ` (locals) and `I` (the ivar spine of the
object `self` denotes). For the rules below tier 3 both are invisible — a literal returns
them unchanged — but neither is cosmetic: Ruby evaluates a send's receiver before its
arguments and its arguments left to right, and any of them may assign to a local *or* to an
instance variable, so the compound rules thread `Γ → Γ₁ → Γ₂` and `I → I₁ → I₂` rather than
typing every part in the same state. -/
inductive Judge : Ctx → Env → Ty → Expr → Ty → Env → Ty → Prop
  /-- An integer literal — including a negative one: `-5` desugars to `int (-5)`, not to
      a unary send (rung 008), so this single rule covers both. -/
  | intLit {κ : Ctx} {Γ : Env} {I : Ty} {n : Int} :
      Judge κ Γ I (.int n) .int Γ I
  /-- A float literal. `Expr.flt` carries IEEE bits; the type does not depend on them,
      so no side condition. -/
  | fltLit {κ : Ctx} {Γ : Env} {I : Ty} {bits : UInt64} :
      Judge κ Γ I (.flt bits) .float Γ I
  /-- A string literal is *an instance of* `String` — `.cls "String"`, never a
      dedicated `str` type; this type language has none (`Ratchet/Ty.lean`). -/
  | strLit {κ : Ctx} {Γ : Env} {I : Ty} {s : String} :
      Judge κ Γ I (.str s) (.cls "String") Γ I
  | symLit {κ : Ctx} {Γ : Env} {I : Ty} {s : String} :
      Judge κ Γ I (.sym s) .sym Γ I
  /-- `true` and `false` share one type. `Ty` has no singleton-`true` type, and Ruby's
      two distinct classes (`TrueClass`/`FalseClass`) are not distinguished here —
      `Ty.bool` covers both, which is why rungs 002 and 003 both target `.bool`. -/
  | truLit {κ : Ctx} {Γ : Env} {I : Ty} : Judge κ Γ I .tru .bool Γ I
  | flsLit {κ : Ctx} {Γ : Env} {I : Ty} : Judge κ Γ I .fls .bool Γ I
  /-- `nil : Nil` — the singleton type, not `nilable` of anything. -/
  | nilLit {κ : Ctx} {Γ : Env} {I : Ty} : Judge κ Γ I .nil .nilT Γ I
  /-- Reading a local: its type is whatever the environment last recorded for it, and
      the read binds nothing. A name *not* in `Γ` has no rule — and correctly so, since
      the desugarer only emits `var lvar x` where Ruby's parser saw an assignment to `x`
      earlier in the same scope; a bare name it did not is a `vcall` (see `bareName`). -/
  | var {κ : Ctx} {Γ : Env} {I : Ty} {x : String} {τ : Ty} :
      envGet? Γ x = some τ → isAliasTy τ = false → Judge κ Γ I (.var .lvar x) τ Γ I
  /-- Reading a local that currently **aliases** another (tier 12): its type is the alias's
      payload, so no expression ever has type `Ty.sameAs`. Split from `var` rather than folded
      into it (as `stripAlias` in the conclusion) for a purely mechanical reason worth recording,
      because it recurs: a conclusion of the form `f τ` for a non-injective `f` cannot be
      unified with a concrete type, so every one of the 137 `Judge.var` uses in `Rungs.lean`
      would have needed its type written out. A `Bool` premise on `τ` instead leaves the
      conclusion's `τ` a bare variable, and the premise discharges by `rfl` once it is
      solved. -/
  | varAlias {κ : Ctx} {Γ : Env} {I : Ty} {x y : String} {τ : Ty} :
      envGet? Γ x = some (.sameAs y τ) → Judge κ Γ I (.var .lvar x) τ Γ I
  /-- Assignment. Its *value* is the right-hand side's (Ruby's `x = e` evaluates to `e`),
      and its *effect* is to record that type for `x` in the outgoing environment.

      `envSet` overwrites, so `x = 1; x = true` simply re-types `x`; nothing here demands
      the new type relate to the old one. That is not a weakness of the checker, it is
      what a Ruby local *is* (rung `reassign-different-type`). Note the ordering: the
      right-hand side is typed in `Γ` and may itself assign (`y = (x = 1) + 1`), so the
      binding is added to `Γ'`, the environment the RHS left behind — not to `Γ`. -/
  | vasgn {κ : Ctx} {Γ Γ' : Env} {I I' : Ty} {x : String} {e : Expr} {τ : Ty} :
      Judge κ Γ I e τ Γ' I' →
      Judge κ Γ I (.vasgn .lvar x e) τ (envSet (killAliasesTo Γ' x) x τ) I'
  /-- **`__dt_t1 = v` — an assignment that records an alias** (tier 12).

      Same value and same effect as `vasgn`; the only difference is what lands in the
      environment, `.sameAs x τ` instead of `τ`. See `Ty.sameAs` for why the alias is needed at
      all (the desugarer's `case`/`&&` temporaries) and why it lives in the environment.

      **Restricted to one of the desugarer's own temporary names** (`desugarTemps`). That
      restriction is not a soundness requirement — the rule would be sound for any name — it is
      a *blast-radius* one, and it buys two things worth having. Every existing rung's recorded
      outgoing environment is unchanged, because no user-written program in the corpus assigns
      to such a name. And the alias mechanism is confined to the construct that needs it, where
      its lifetime is a couple of statements inside one `seq` and the invalidation story is easy
      to check by reading.

      The three invalidations. **Assignment to the holder** overwrites the binding, so nothing
      is needed. **Assignment to the target** is `vasgn`'s `killAliasesTo` above: once `v` holds
      a new object, `__dt_t1` no longer holds the same one. **A block reassigning a captured
      local** is the one that is not visible as an assignment at all — the rules that carry a
      caller's environment out across a block call justify doing so with `capIntact`, which
      compares *types*, and a value can change at a fixed type; so those rules apply
      `killAliases` to what they carry out. That list is `closCall`, `yieldExpr`, `iterBlock`,
      `iterClosPass`, `callDefBlk`, `callMethodBlk`, `callSMethodBlk`, `selfCallBlk` — every
      rule in the judgment through which a block body can run.

      A fourth case needs no rule: a branch that invalidates in one arm and not the other loses
      the alias at the join, because `joinT (sameAs y τ) τ` is a `union`, and a `union` is not a
      `sameAs`. -/
  | vasgnAlias {κ : Ctx} {Γ : Env} {I : Ty} {t x : String} {σ τ : Ty} :
      desugarTemps.contains t = true → envGet? Γ x = some σ → stripAlias σ = τ →
      Judge κ Γ I (.vasgn .lvar t (.var .lvar x)) τ
        (envSet (killAliasesTo Γ t) t (.sameAs x τ)) I
  /-- A statement sequence: the whole thing has the *last* statement's type, and both
      threaded states flow through all of them. Delegated to `JudgeSeq` so the non-empty
      requirement is structural, and because `JudgeSeq` is also where the *syntax tables*
      thread (a `def` or a `class` is visible to the statements after it and to nothing
      else — see `DefTable`). -/
  | seq {κ : Ctx} {Γ Γ' : Env} {I I' : Ty} {es : List Expr} {τ : Ty} :
      JudgeSeq κ Γ I es τ Γ' I' → Judge κ Γ I (.seq es) τ Γ' I'
  /-- A bare identifier that is not a local: `x` desugars to `vcall "x"`, a method-call
      attempt on implicit `self`. When the name resolves to nothing (`BareNameError`),
      evaluating it raises `NameError` — which is *outside* the
      `NoMethodError`/`ArgumentError`/`TypeError` family this ladder defines type-safety
      over, exactly as `ZeroDivisionError` is (see `PrimSig.intDiv`). So the program is
      type-safe despite crashing, and the type recorded is `.any`: the expression never
      produces a value, so nothing downstream can depend on it — and `.any` matches no
      `PrimSig` row and is not `EqSafe`, so no rule can consume it either. Type safety
      here is not crash-freedom, and this rung is the sharpest place that shows.

      **Two guarding premises, added in the two tiers that could have broken this rule.**

      `defGet? κ.defs m = none` is tier 6's. Until then no rule typed a `def'`, so a
      program that defined `x` and then called it bare could not be judged at all, and that
      accident was what made the one `BareNameError` row sound. With `defStmt` in place,
      `def x; 1 + true; end; x` would otherwise take this route to `.any` and validate a
      program that raises `TypeError`. The premise restores the property by *checking* it.

      `κ.selfTy = none` is tier 7's, and it is the same failure one level down: inside a
      method body a bare name resolves against *that object*, so a `vcall "x"` in a `Point`
      method with a `Point#x` would launder the same way. Restricting the rule to top level
      is the honest fix — the docstring of every earlier version of it already said the rule
      assumed top-level `self`, and now it says so in the premise. Implicit-self dispatch
      inside a body is `selfCall`'s job instead.

      Remaining conservatism, recorded: there is no rule for a top-level `vcall` that *does*
      name a defined method (`def get5; 5; end; get5`, no parentheses — the desugarer emits
      a `vcall`, not an argument-less `send`). Such a program is simply not typed. -/
  | bareName {κ : Ctx} {Γ : Env} {I : Ty} {m : String} :
      BareNameError m → defGet? κ.defs m = none → κ.selfTy = none →
      Judge κ Γ I (.vcall m) .any Γ I
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
      ends up at a union that no rule can consume.

      **The ivar spine is joined too, and that changed at tier 12.** Clink 6 made `I₁ = I₂` a
      *premise* rather than a join, arguing that a spine is part of the **type** of `self`
      (see `Ty.inst`) and that no pointwise widening of it keeps that type honest. Narrowing is
      what makes the widening honest — `@v : union Int String` is now something a branch can
      consume — so the premise is now `joinSpine I₁ I₂ = I₃`, with `I₃` the outgoing spine.
      That is strictly more permissive, and it is what makes `narrow-union-in-ivar` typeable:
      `if flag then @v = 1 else @v = "s" end` used to have no derivation at all.

      Why it is still written as a premise-plus-index rather than putting `joinSpine I₁ I₂`
      straight in the conclusion: `joinSpine I I = I` holds *definitionally*, so every
      derivation term written against the old `I₁ = I₂` premise discharges the new one with the
      same `rfl`, and none of the 96 on file had to be edited.

      **Each branch is typed in a *narrowed* environment** (tier 12). This is the one part
      of the rule that is a claim about Ruby's *dynamic* behaviour rather than about the
      shape of the judgment: if control reached the then-branch, the condition evaluated
      truthy, and for a condition of a recognized shape that is information about a local's
      type. `narrowEnvs` is where that information is computed, and it is a total function
      that is the **identity** on every condition it does not recognize — so this premise
      reads exactly as it did before tier 12 for every earlier rung, and every derivation
      written before tier 12 still type-checks unchanged.

      Why it lives here rather than in a separate `ifNarrow` rule: two rules for one
      syntactic form would mean the honest reading of "what does this checker believe about
      `if`" requires reading both and knowing which one `chk` reaches. One rule with a
      possibly-trivial refinement has a single reading.

      Why it is not a *rewrite* of the program: the refinement's justification is the
      branch it is applied in, and the branch bodies do not mention the condition. There is
      no substitution that could express it — see `implementation-notes.md` clink 12, and
      `NarrowCond` for what evaluating the condition is required not to do. -/
  | if' {κ : Ctx} {Γ Γc Γ₁ Γ₂ : Env} {I Ic I₁ I₂ I₃ : Ty} {c t e : Expr}
      {σ τ₁ τ₂ : Ty} :
      Judge κ Γ I c σ Γc Ic →
      Judge κ (narrowEnvs κ.classes c Γc).1 (narrowSpine κ.classes c Ic).1 t τ₁ Γ₁ I₁ →
      Judge κ (narrowEnvs κ.classes c Γc).2 (narrowSpine κ.classes c Ic).2 e τ₂ Γ₂ I₂ →
      joinSpine I₁ I₂ = I₃ →
      Judge κ Γ I (.if' c t (some e)) (joinT τ₁ τ₂) (joinEnv Γ₁ Γ₂) I₃
  /-- `if c then t end`, with no `else`. Ruby's missing branch evaluates to `nil`, so
      this is the same rule with the else-branch's type fixed at `.nilT` and its
      environment fixed at `Γc` — the state as of the end of the condition.
      `joinT τ .nilT` is `mkNilable τ` (rung `if-no-else`). The absent branch cannot touch
      the ivar spine, so the same agreement premise reads `I₁ = Ic`.

      Tier 12's narrowing applies to both halves for the same reasons as in `if'`, and the
      *else* half is worth a second look: the missing branch still **runs**, in the sense
      that control flows past the `if` having taken it, so what the code after the `if`
      sees on that path is `(narrowEnvs κ.classes c Γc).2`, not `Γc`. Using `Γc` would be sound
      but strictly less precise; using `.1` would be a bug. The spine is treated the same way,
      and its premise is the `joinSpine` of `if'`, with the absent branch's refined spine in
      place of a second branch's. -/
  | ifNoElse {κ : Ctx} {Γ Γc Γ₁ : Env} {I Ic I₁ I₂ : Ty} {c t : Expr} {σ τ : Ty} :
      Judge κ Γ I c σ Γc Ic →
      Judge κ (narrowEnvs κ.classes c Γc).1 (narrowSpine κ.classes c Ic).1 t τ Γ₁ I₁ →
      joinSpine I₁ (narrowSpine κ.classes c Ic).2 = I₂ →
      Judge κ Γ I (.if' c t none) (joinT τ .nilT)
        (joinEnv Γ₁ (narrowEnvs κ.classes c Γc).2) I₂
  /-- An array literal. The elements are typed left to right — `JudgeAll` already
      threads both states in exactly Ruby's element-evaluation order, so this rule
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
  | arrayLit {κ : Ctx} {Γ Γ' : Env} {I I' : Ty} {es : List Expr} {τs : List Ty} :
      JudgeAll κ Γ I es τs Γ' I' → Judge κ Γ I (.array es) (.arrayOf (elemTy τs)) Γ' I'
  /-- A hash literal, typed as the bare `.cls "Hash"`.

      **The key and value types are discarded, and the premise is still not vacuous.**
      `Ty` has no parameterised hash constructor (no `hashOf` beside `arrayOf`), so there
      is nowhere to record what a hash maps to — but every key and every value expression
      must still be *typeable*, because evaluating one can be type-stuck all on its own
      (`{"a" => 1 + "b"}` must not type). `JudgePairs` is what carries that requirement,
      and it also threads in Ruby's order: key then value, pair by pair.

      This is the rung the corpus records as a `Ty` language gap rather than a missing
      rule, and `PrimSig.hashIndex` is where the gap becomes visible. -/
  | hashLit {κ : Ctx} {Γ Γ' : Env} {I I' : Ty} {pairs : List (Expr × Expr)} :
      JudgePairs κ Γ I pairs Γ' I' → Judge κ Γ I (.hash pairs) (.cls "Hash") Γ' I'
  /-- A top-level `def` **statement**. Its type is `.sym`: `def foo; end` evaluates to
      `:foo` in Ruby, which is easy to forget because nobody uses the value.

      **The body is not checked here, and that is correct rather than lazy.** A method that
      is never called never runs, so `def bad(x); x + true; end` with no call site is
      perfectly safe Ruby and validates. What the rule *does* is nothing at all to the
      environment — a `def` binds no local — while `JudgeSeq.cons` separately extends the
      def table with it (see `extendDefs`). Keeping those two effects in different places is
      deliberate: the type of a `def` is a fact about the expression, whereas its effect on
      the table is a fact about *statement order*, and only `JudgeSeq` knows about order.

      The body's obligation arrives instead at each call site, via `callDef`. -/
  | defStmt {κ : Ctx} {Γ : Env} {I : Ty} {n : String}
      {ps : List Param} {body : Expr} :
      Judge κ Γ I (.def' n ps body) .sym Γ I
  /-- A call to a method whose instantiation is **assumed**.

      On its own this rule is unsound in the most obvious way: `κ.asms` is an index, so a
      derivation may start from any assumption table at all. It is sound *in context*
      because `callDef` below is the only rule that ever grows it, and it grows it by
      exactly the assumption it then discharges — so a derivation with an empty table,
      which is where `validate` starts, contains no undischarged assumption. See
      `AsmTable`.

      The lookup is keyed by the argument types as well as the name, because this checker
      has no notion of "the" signature of a method: it types a body once per call-site
      argument shape. -/
  | callAsm {κ : Ctx} {Γ Γ' : Env} {I I' : Ty} {m : String}
      {args : List Expr} {argTys : List Ty} {ρ : Ty} :
      JudgeAll κ Γ I args argTys Γ' I' → asmGet? κ.asms m argTys = some ρ →
      Judge κ Γ I (.send none m args none) ρ Γ' I'
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
      - **The caller's state is untouched.** The outgoing locals are `Γ'` — the caller's,
        after the arguments — never the body's. A Ruby method body neither sees nor writes
        the caller's locals. The body's own ivar spine is `.ivar0` and must come back
        `.ivar0`: a *top-level* method runs with `self` = main, whose instance variables this
        judgment does not model, so a body that assigns one is simply not typed.

      **Recursion, and why the assumption is discharged rather than believed.** `fact`
      calls itself, so its body cannot be judged before its return type is known, and its
      return type comes from its body. The cycle is broken by *assume-then-verify*: `ρ`
      appears in the premise as an assumption (`(m, argTys, ρ)` pushed onto `κ.asms`, which
      `callAsm` picks up at the recursive occurrence) **and** as the type the body must
      synthesize under that assumption. Nothing here says where `ρ` came from;
      `Ratchet/Validate.lean` finds a candidate by typing the body once with the recursive
      call at `.never` and then *re-runs* the check with the candidate in place. The first
      pass is an untrusted hint — a wrong hint fails the second pass — which is why no
      version of it appears in this rule.

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
  | callDef {κ : Ctx} {Γ Γ' Γb Γb' : Env} {I I' : Ty} {m : String}
      {args : List Expr} {argTys : List Ty} {d : Defn} {ρ : Ty} :
      JudgeAll κ Γ I args argTys Γ' I' → defGet? κ.defs m = some d →
      paramEnv d.params argTys = some Γb →
      Judge { κ with asms := ⟨m, argTys, ρ⟩ :: κ.asms } Γb .ivar0 d.body ρ Γb' .ivar0 →
      Judge κ Γ I (.send none m args none) ρ Γ' I'
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
  | primNever {κ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty} {recv : Expr}
      {m : String} {args : List Expr} {σ : Ty} {argTys : List Ty} :
      Judge κ Γ I recv σ Γ₁ I₁ → JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      (σ = .never ∨ argTys.contains .never = true) →
      Judge κ Γ I (.send (some recv) m args none) .never Γ₂ I₂
  /-- Strictness for an implicit-self call: the same argument as `primNever`, with no
      receiver to consider. Placed *before* `callAsm`/`callDef` in `Validate.lean`'s
      match, so a call with a non-returning argument is `.never` whether or not the method
      is defined — which is right: an undefined method is never reached either. -/
  | callNever {κ : Ctx} {Γ Γ' : Env} {I I' : Ty} {m : String}
      {args : List Expr} {argTys : List Ty} :
      JudgeAll κ Γ I args argTys Γ' I' → argTys.contains .never = true →
      Judge κ Γ I (.send none m args none) .never Γ' I'
  -- ### Tier 7 — the object model
  --
  -- Eight rules. `classStmt`/`constCls` are the declaration side; `newInst`/
  -- `newInstNoInit`/`callMethod`/`selfCall` are dispatch; `selfExpr`/`ivarRead`/`ivarAsgn`
  -- are the state. Inheritance, `super` and singleton methods are a separate tier-7 clink
  -- and have no rule here.
  /-- A `class` declaration statement.

      **Its type is `.any` because a class body's value is its last statement's**
      (`class Foo; def hi; end; end` really evaluates to `:hi`), and nothing in the corpus
      reads it. `.any` is sound and inert, so the imprecision cannot leak; a rung that used
      the value would need this rule split by body shape.

      **The premise is the load-bearing part.** `classMethods? body = some ms` restricts the
      body to a `def`, a sequence of `def`s, or `nil` — which is simultaneously what makes
      the body safe to *evaluate* unchecked (a `def` statement never runs its body, and
      `nil` is `nil`) and what makes the class readable into `CTable` by `extendClasses`.
      A class body containing anything else is not typed at all, which is conservative in
      the direction that costs rungs rather than soundness.

      As with `defStmt`, this rule does nothing to any table; `JudgeSeq.cons` extends
      `κ.classes` separately, because only `JudgeSeq` knows statement order.

      **The second premise arrived with tier 10's mixins** and is a soundness requirement, not
      a tidiness one: `classMethods?` now accepts `include M`/`extend M` in the body, and
      `include` on anything that is not a `Module` raises `TypeError` — inside the family. So
      every mixed-in name has to be a declared `module` (`allModules`), which also has the
      effect of refusing a name the table does not know at all. -/
  | classStmt {κ : Ctx} {Γ : Env} {I : Ty} {n : String} {sup : Option Expr}
      {body : Expr} {ms sms : List Defn} {incs exts preps : List String} :
      classMethods? body = some (ms, sms, incs, exts, preps) →
      allModules κ.classes (incs ++ exts ++ preps) = true →
      Judge κ Γ I (.class' n sup body) .any Γ I
  /-- A constant naming a declared class, as a **class object** — `.clsOf n`, which
      `Ratchet/Ty.lean` distinguishes from `.cls n` (an instance of it) precisely so that
      `Point` and `Point.new` cannot be confused. Only declared classes get a rule: a
      constant this checker has never seen a `class` statement for is not typed, so
      `Undeclared.new` fails here rather than at dispatch. -/
  | constCls {κ : Ctx} {Γ : Env} {I : Ty} {n : String} {c : Cls} :
      clsGet? κ.classes n = some c → Judge κ Γ I (.const n) (.clsOf n) Γ I
  /-- **A constant naming a *builtin* class** (tier 12). Same conclusion as `constCls` —
      `.clsOf n` — for a class the program did not declare.

      Why this needs its own rule rather than seeding `CTable` with builtin entries: a
      `CTable` row carries method tables, and `mroGet?`/`ctorGet?` would then happily
      dispatch and *allocate* against them. `Integer.new` would find the zero-argument
      allocator and validate, and it raises `NoMethodError`. Keeping builtins out of the
      table means the only thing this rule licenses is the class object's *identity*, which
      is all `is_a?` needs.

      The `clsGet? = none` premise makes the two `const` rules disjoint, so a program that
      reopens `class Integer` (which would put `Integer` in the table) goes through
      `constCls` and this rule stays out of the way.

      `BuiltinCls` is deliberately just the classes `builtinAncestors` covers plus the two
      boolean ones: a name admitted here but absent from `builtinAncestors` would produce a
      `.clsOf` nobody can answer `is_a?` for, which is inert but pointless. -/
  | constBuiltin {κ : Ctx} {Γ : Env} {I : Ty} {n : String} :
      BuiltinCls n → clsGet? κ.classes n = none →
      Judge κ Γ I (.const n) (.clsOf n) Γ I
  /-- **`C.new(args)` — allocation, and where an instance's type is manufactured.**

      The receiver must be a class object (`.clsOf n`), so this rule is reached through
      `constCls`. What it produces is `.inst n Iout`, and `Iout` — the ivar spine — is the
      whole content of the rule: it is computed by *judging `initialize`'s body* with the
      call's argument types as its parameters and the empty spine as its state, and taking
      the spine that comes out.

      That is why `Ty.inst` carries ivars at all. Ruby declares no ivar types, so the only
      moment the information exists is this one, and the only place to keep it is the type
      of the object. `Point.new(1, 2)` and `Point.new("a", "b")` get *different* types from
      the same class, which is what makes `getX` return an `Integer` from one and a
      `String` from the other with no annotation anywhere (rung `class-basic`).

      **`self` is not typed inside `initialize`.** The context is `κ` unchanged, so
      `κ.selfTy` is whatever the caller's was, and in every rung that is `none`. The reason
      is not laziness: `initialize`'s job is to *change* the spine, so there is no single
      spine that describes `self` throughout it, and therefore no honest `.inst n _` to
      offer. A method called on `self` from inside `initialize` would read a spine that is
      still being built, and claim `nil` for an ivar that is about to be an `Integer` —
      unsound. Refusing to type `self` there is the conservative fix; a rule that wants it
      needs a fixpoint over the spine, and no rung asks. -/
  | newInst {κ : Ctx} {Γ Γ₁ Γ₂ Γb Γb' : Env} {I I₁ I₂ Iout : Ty} {recv : Expr}
      {n dc : String} {args : List Expr} {argTys : List Ty} {d : Defn}
      {ρ : Ty} :
      Judge κ Γ I recv (.clsOf n) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      ctorGet? κ.classes n = some (dc, d) →
      paramEnv d.params argTys = some Γb →
      Judge (κ.inCtor n dc "initialize") Γb .ivar0 d.body ρ Γb' Iout →
      Judge κ Γ I (.send (some recv) "new" args none) (.inst n Iout) Γ₂ I₂
  /-- `C.new` for a class with **no `initialize`**: the object starts with no instance
      variables, so its spine is `.ivar0`.

      A separate rule rather than a defaulting clause inside `newInst`, because the arity
      condition is different and it matters: `Object#new` inherited unchanged takes **zero**
      arguments, and passing any raises `ArgumentError` — inside the family. Hence
      `argTys = []` as a premise (rungs `class-no-initialize`, `class-ivar-lazy-nil`). -/
  | newInstNoInit {κ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty} {recv : Expr}
      {n : String} {args : List Expr} {c : Cls} :
      Judge κ Γ I recv (.clsOf n) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args [] Γ₂ I₂ →
      instClsGet? κ.classes n = some c → ctorGet? κ.classes n = none →
      Judge κ Γ I (.send (some recv) "new" args none) (.inst n .ivar0) Γ₂ I₂
  /-- **An instance method call.** The receiver's type carries both halves of what dispatch
      needs: `.inst n Iself` says which class to look the method up in *and* what the
      object's instance variables are, so the body is judged with `Iself` as its state and
      `some (.inst n Iself)` as the type of `self`.

      **The last premise's outgoing spine is `Iself` again, and that equation is the
      soundness argument for the whole ivar mechanism.** It says a method may not change any
      instance variable's *type* — not widen it, not add a new one. Without it, a caller
      holding `.inst n Iself` would keep using a stale spine after the callee had
      invalidated it, and the `nil` that `ivarRead` hands back for an absent ivar would be a
      lie for objects some other method had since initialized. With it, a spine built by
      `initialize` is **stable and complete** for the object's whole life, which is exactly
      the invariant `ivarRead`'s defaulting depends on.

      What it costs: `def set(v); @v = v; end` called at a type other than `@v`'s is
      rejected, as is any method that lazily creates an ivar. `class-setter-method`
      (`@size = @size + 1`) passes because `Integer + Integer` is an `Integer` — the type is
      unchanged even though the value is not. That rung is exactly the boundary case.

      **No assumption table for methods.** Unlike `callDef`, this rule has no
      assume-then-verify machinery, so a directly or mutually recursive method exhausts
      `chk`'s fuel and is rejected. Conservative, and no rung asks for it; the fix, if one
      is ever wanted, is to key `AsmTable` by receiver type as well as name. -/
  | callMethod {κ : Ctx} {Γ Γ₁ Γ₂ Γb Γb' : Env} {I I₁ I₂ Iself : Ty} {recv : Expr}
      {m : String} {args : List Expr} {argTys : List Ty} {n dc : String}
      {d : Defn} {ρ : Ty} :
      Judge κ Γ I recv (.inst n Iself) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      mroGet? κ.classes n m = some (dc, d) →
      paramEnv d.params argTys = some Γb →
      Judge (κ.inMethod (.inst n Iself) dc m) Γb Iself d.body ρ Γb' Iself →
      Judge κ Γ I (.send (some recv) m args none) ρ Γ₂ I₂
  /-- **`method_missing` — dispatch found nothing, so the object gets asked** (tier 10).

      `Ghost.new.anything_at_all` with `def method_missing(name); "called " + name.to_s; end`.
      Mechanically this is `callMethod` with two changes: the name looked up is
      `"method_missing"` rather than `m`, and the argument list gains a **`.sym` in front** —
      Ruby passes the missing name as a Symbol, then the original arguments. `paramEnv`'s
      arity check then does the rest, which is why `metaprog-method-missing-fixed-arity`
      validates and its splat sibling does not (see §Ty language gaps: `*args` has no `Ty`).

      **Two premises decide whether this rule is sound, and they are about *when it fires*, not
      about what it does.**

      `mroGet? κ.classes n m = none` is the obvious one: `method_missing` is a fallback, and a
      fallback that can fire while an ordinary method exists would give the wrong type for every
      call.

      `¬ ObjectMethod m` is the one that is easy to miss. This judgment's class table holds only
      what the *program* declared, so `mroGet?` misses for `to_s`, `inspect`, `hash`, `==`,
      `class` — every method `Object` provides — and Ruby runs those, not `method_missing`.
      Without the premise, `Ghost.new.to_s` would be typed as `"called to_s"` while really
      producing `#<Ghost…>`: not a rejection, a **wrong answer**. `ObjectMethod`'s docstring
      says why that table is the one place on this ladder where completeness is the soundness
      condition.

      Restricted to an explicit receiver. A *bare* missing name inside a method body is a
      `vcall`, and `selfCall`'s miss would want the same fallback with `κ.selfTy`'s class; no
      rung writes one, and it would be this rule copied. -/
  | callMissing {κ : Ctx} {Γ Γ₁ Γ₂ Γb Γb' : Env} {I I₁ I₂ Iself : Ty} {recv : Expr}
      {m : String} {args : List Expr} {argTys : List Ty} {n dc : String}
      {d : Defn} {ρ : Ty} :
      Judge κ Γ I recv (.inst n Iself) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      mroGet? κ.classes n m = none →
      ¬ ObjectMethod m →
      mroGet? κ.classes n "method_missing" = some (dc, d) →
      paramEnv d.params (.sym :: argTys) = some Γb →
      Judge (κ.inMethod (.inst n Iself) dc "method_missing") Γb Iself d.body ρ Γb' Iself →
      Judge κ Γ I (.send (some recv) m args none) ρ Γ₂ I₂
  /-- **Implicit-self dispatch inside a method body**: a bare name that names one of the
      object's own methods. `class Rect; def describe; "area=" + area.to_s; end; …` — the
      `area` there is a `vcall`, not a local read and not a top-level function call, and it
      is what `class-method-calls-method` needs.

      `κ.selfTy` supplies the receiver, so this rule is only available inside a body, which
      is also why `bareName` had to grow its `κ.selfTy = none` premise: without that, the two
      rules would overlap on a name that is both a `BareNameError` row and a method of
      `self`, and the wrong one would answer.

      Zero arguments, because a `vcall` *is* the zero-argument bare-name form (an
      implicit-self call with arguments is `send none m args`, which goes to
      `callDef`/`callAsm`). Extending that to instance methods is what tier 7's second clink
      needs for `super`, and is deliberately not done here. -/
  | selfCall {κ : Ctx} {Γ Γb Γb' : Env} {I Iself : Ty} {m : String} {n dc : String}
      {d : Defn} {ρ : Ty} :
      κ.selfTy = some (.inst n Iself) →
      mroGet? κ.classes n m = some (dc, d) →
      paramEnv d.params [] = some Γb →
      Judge (κ.inMethod (.inst n Iself) dc m) Γb Iself d.body ρ Γb' Iself →
      Judge κ Γ I (.vcall m) ρ Γ I
  -- ### Tier 7's hierarchy
  --
  -- Three rules, and each one is about a place where "which class?" has a different answer
  -- from the obvious one: `super` needs the *definition site*, a singleton method needs the
  -- *other* method table, and a bare `new` inside a singleton method needs `self` to be a
  -- class object rather than an instance.
  /-- **`super(args)`** — delegate to the same method name, one class further up.

      **`super` is "keep going from where I was found", in the *receiver's* MRO** — and both
      halves of that are why `Ctx.frame` exists. `defClass` (the definition site) says where to
      resume from: in `class Triangle < Shape; def initialize; super(3); end`, the parent to run
      is found after `Triangle`, the class this running method was declared in, which for a
      deeper hierarchy is a different answer from "after the receiver's class". `recvClass` says
      *which* MRO to resume in, and that half arrived with tier 10's `prepend`: for a prepended
      module the next entry is the class that prepended it, which nothing about the module names.
      `κ.selfTy` cannot supply either — inside `initialize` it is not even set.

      Stated as a list operation the rule is short: build the receiver's MRO, drop everything up
      to and including `defClass`, and search the rest. Tier 7's `c.super?` walk was the special
      case of that for an MRO with no mixins in it.

      **The ivar spine threads *through* the super call.** The body is judged with `I'` — the
      spine as of the end of the arguments — and its outgoing spine `Iout` becomes the super
      call's. That is exactly right for the constructor case this rung is: `Shape#initialize`
      is *continuing to build the same object*, so `super(3)` is where `@sides` gets set, and
      `newInst` picks the finished spine up from the whole body.

      The frame is *rebuilt* for the parent body (`dc`, the class the parent method was found
      in), so a `super` inside the parent walks from the right place again. Zero-argument
      `super` (`zsuper`, which forwards the current method's arguments implicitly) is a
      different `Expr` head and has no rule. -/
  | superCall {κ : Ctx} {Γ Γ' Γb Γb' : Env} {I I' Iout : Ty} {args : List Expr}
      {argTys : List Ty} {fr : Frame} {mro rest : List String} {dc : String} {d : Defn}
      {ρ : Ty} :
      JudgeAll κ Γ I args argTys Γ' I' →
      κ.frame = some fr →
      mroList? κ.classes fr.recvClass = some mro →
      afterInMro mro fr.defClass = some rest →
      searchMro κ.classes rest fr.methName = some (dc, d) →
      paramEnv d.params argTys = some Γb →
      Judge { κ with frame := some ⟨fr.recvClass, dc, fr.methName⟩ } Γb I' d.body ρ Γb' Iout →
      Judge κ Γ I (.super' args none) ρ Γ' Iout
  /-- **`super` with no argument list** (`zsuper`) — forwards the running method's own
      arguments implicitly.

      Tier 10's `metaprog-prepend` is the first rung to write one, and it writes the easy case:
      a method with **no parameters**, where "forward my arguments" forwards nothing. That is
      what the second and third premises pin down — `mroGet?` from the receiver's class finds
      the running method (necessarily at `fr.defClass`, since that is how dispatch got here) and
      its parameter list has to be empty. The rest is `superCall` with `argTys = []`.

      **Why the arity premise is a soundness requirement and not tidiness.** `zsuper` forwards
      the current method's arguments to the parent, so if the two arities disagree Ruby raises
      `ArgumentError` — inside the family. `paramEnv d.params []` already forces the *target* to
      take none; `dcur.params = []` is the other half.

      The general rule wants the running method's parameter list, at the types those locals hold
      **now** (Ruby forwards current values, so a reassigned parameter forwards its new one),
      which means putting the parameter list in `Frame` beside `methName`. Every body-entering
      rule has the `Defn` at hand, so that is mechanical rather than deep; no rung asks. -/
  | zsuperCall {κ : Ctx} {Γ Γb Γb' : Env} {I Iout : Ty} {fr : Frame}
      {mro rest : List String} {dc : String} {dcur d : Defn} {ρ : Ty} :
      κ.frame = some fr →
      mroGet? κ.classes fr.recvClass fr.methName = some (fr.defClass, dcur) →
      dcur.params = [] →
      mroList? κ.classes fr.recvClass = some mro →
      afterInMro mro fr.defClass = some rest →
      searchMro κ.classes rest fr.methName = some (dc, d) →
      paramEnv d.params [] = some Γb →
      Judge { κ with frame := some ⟨fr.recvClass, dc, fr.methName⟩ } Γb I d.body ρ Γb' Iout →
      Judge κ Γ I (.zsuper none) ρ Γ Iout
  /-- **A singleton ("class") method call**: `Point.origin`. The receiver is a class object,
      so lookup goes to the *other* table (`smroGet?`, which walks `super?` as well — Ruby
      inherits class methods), and the body is judged with `self` typed as
      **`.clsOf n`** rather than as an instance. That last part is the whole point: it is what
      lets the body's bare `new(0, 0)` mean "allocate one of me" (see `selfNew`).

      Tried *before* `new` in `Validate.lean`'s match, so a class that defines `self.new` gets
      its own rather than the allocator — which is what Ruby does.

      The body's ivar state is `.ivar0` in and out. A class object can hold instance variables
      of its own (`@count` at class level), and this judgment does not model them, so a
      singleton method that assigns one is not typed. -/
  | callSMethod {κ : Ctx} {Γ Γ₁ Γ₂ Γb Γb' : Env} {I I₁ I₂ : Ty} {recv : Expr}
      {m : String} {args : List Expr} {argTys : List Ty} {n dc : String}
      {d : Defn} {ρ : Ty} :
      Judge κ Γ I recv (.clsOf n) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      smroGet? κ.classes n m = some (dc, d) →
      paramEnv d.params argTys = some Γb →
      Judge (κ.inMethod (.clsOf n) dc m) Γb .ivar0 d.body ρ Γb' .ivar0 →
      Judge κ Γ I (.send (some recv) m args none) ρ Γ₂ I₂
  /-- **A bare `new(args)` inside a singleton method**: `def self.origin; new(0, 0); end`.

      An implicit-self send whose `self` is a class object, so it allocates. Everything else
      is `newInst`'s — `initialize`'s body judged at the argument types, the resulting spine
      becoming the instance's type — and the two rules would be one if the receiver came from
      the same place.

      Only `new` gets this treatment, and only with an `initialize` present. A bare call to
      *another* singleton method from inside one, or to `new` on a class without an
      `initialize`, would each be another rule of the same shape; no rung asks. -/
  | selfNew {κ : Ctx} {Γ Γ' Γb Γb' : Env} {I I' Iout : Ty} {args : List Expr}
      {argTys : List Ty} {n dc : String} {d : Defn} {ρ : Ty} :
      κ.selfTy = some (.clsOf n) →
      JudgeAll κ Γ I args argTys Γ' I' →
      ctorGet? κ.classes n = some (dc, d) →
      paramEnv d.params argTys = some Γb →
      Judge (κ.inCtor n dc "initialize") Γb .ivar0 d.body ρ Γb' Iout →
      Judge κ Γ I (.send none "new" args none) (.inst n Iout) Γ' I'
  -- ### Tier 8 — modules
  --
  -- Two rules, and the smallness is the finding: `M.foo` for a `def self.foo` is
  -- `callSMethod` with nothing added, because a module *is* an object with a singleton method
  -- table. All that was genuinely missing was a statement rule and the bare-name form.
  /-- A `module` declaration statement. `.any` for the same reason `classStmt` is — a module
      body's value is its last statement's — and the same `classMethods?` premise, doing the
      same double duty (safe to evaluate unchecked, and readable into `CTable`).

      Separate from `classStmt` only because `Expr.module'` has no superclass slot; the entry
      it produces differs by `Cls.isModule`, which exists to stop `M.new`. -/
  | moduleStmt {κ : Ctx} {Γ : Env} {I : Ty} {n : String} {body : Expr}
      {ms sms : List Defn} {incs exts preps : List String} :
      classMethods? body = some (ms, sms, incs, exts, preps) →
      allModules κ.classes (incs ++ exts ++ preps) = true →
      Judge κ Γ I (.module' n body) .any Γ I
  /-- A bare name inside a **singleton** method body naming another of the same object's
      singleton methods: `module M; def self.describe; value * 2; end; def self.value; 21;
      end; end`.

      `selfCall`'s twin, for the case where `self` is a class-or-module object rather than an
      instance — the difference is which table the lookup goes to, and it is not a detail: an
      instance method and a singleton method of the same name are different methods, and
      `M.value` resolving to a plain `def value` would be wrong. Zero arguments, because a
      `vcall` is the zero-argument bare-name form. -/
  | selfSCall {κ : Ctx} {Γ Γb Γb' : Env} {I : Ty} {m : String} {n dc : String}
      {d : Defn} {ρ : Ty} :
      κ.selfTy = some (.clsOf n) →
      smroGet? κ.classes n m = some (dc, d) →
      paramEnv d.params [] = some Γb →
      Judge (κ.inMethod (.clsOf n) dc m) Γb .ivar0 d.body ρ Γb' .ivar0 →
      Judge κ Γ I (.vcall m) ρ Γ I
  -- ### Tier 9 — callable values
  --
  -- Two rules, and between them they are `callDef` again with the def table replaced by
  -- `Ctx.closures` and the name replaced by an index carried in the type. See `Ty.clos` for
  -- why the type is a reference to code rather than an arrow.
  /-- **`lambda { |x| … }` / `proc { |x| … }`** — a callable value.

      Both spellings get the same rule and the same type, which is a **known imprecision, not
      an oversight**: a lambda checks its arity strictly and a proc does not (a proc pads
      missing parameters with `nil` and drops extras). `Ty` cannot express the second
      discipline — that is the gap `AGENTS.md` §Ty language gaps records, reached from tier
      9's `proc-arity-leniency` — so this rule imposes the *strict* reading on both.
      Direction matters: strict-for-a-lambda is exact, and strict-for-a-proc rejects legal
      calls, so both errors are conservative. The alternative (lenient for both) would accept
      `lambda-arity-mismatch`, which raises.

      Three premises worth reading:

      - **`locals = []`** (in the pattern): a `|x; y|` block-local list is not modelled, so a
        block with one is not typed. Rung `block-doend-with-block-local` needs it and is not
        in this clink.
      - **`closIdx?`** finds the block in the whole-program table. A block the collector did
        not reach has no index and no derivation.
      - **The creation site's `self` goes in the type** (tier 11). Until then this rule had a
        `κ.selfTy = none` premise instead, restricting creation to top level, because a
        closure's body sees the `self` of wherever it was *created* and `Ty.clos` recorded only
        the captured locals. `Ty.clos`'s third field is that omission fixed — see its
        docstring — so a lambda may now be created anywhere, and `closCall` judges its body
        against the recorded `self` rather than the caller's. -/
  | lambdaLit {κ : Ctx} {Γ : Env} {I : Ty} {m : String} {ps : List Param}
      {body : Expr} {idx : Nat} :
      (m = "lambda" ∨ m = "proc") →
      closIdx? κ.closures ps body = some idx →
      Judge κ Γ I (.send none m [] (some (.block ps [] body)))
        (.clos idx (envToSpine Γ) (κ.selfTy.getD .never)) Γ I
  /-- **`f.call(args)` / `f[args]`** — invoke a callable, by checking its body here.

      The body is judged in `paramEnv c.params argTys ++ spineToEnv cap`: this call site's
      argument types for the parameters, then the locals the lambda captured at creation.
      Parameters come first so they shadow a captured name of the same spelling, which is
      what Ruby does.

      That single environment is the whole of tier 9a. `lambda-closure-capture` works because
      `spineToEnv cap` still holds `n`; `lambda-returns-lambda` works because the inner
      lambda's captured `x` is the *outer's parameter*, which was in `Γ` when the inner
      literal was reached; `lambda-as-argument` works because a `.clos` travels through
      `paramEnv` like any other type.

      `[]` is admitted alongside `call` because `p[3]` is Ruby's other spelling of it (rung
      `proc-bracket-call`) — and note it cannot collide with `PrimSig.arrayIndex`, whose
      receiver is an `arrayOf`.

      Two things go in and come back unchanged, for the same reason and by the same argument
      `callMethod` makes about instance variables: the **ivar spine**, and — via `capIntact` —
      every **captured local**. A body that retyped either would invalidate the caller's view
      of it, and for captured locals that is not hypothetical: see `capIntact`.
      **The body is judged in `κ.inClosure σ`, at the creation site's spine** (tier 11) —
      *not* in the caller's context, which is what this rule used to do behind a
      `κ.selfTy = none` premise that constrained the caller rather than the closure. The old
      shape made `xc-lambda-in-ivar` (`@f.call(v)` inside a method) underivable even though
      the lambda in question was made at top level. Note both halves of the fix are needed:
      `selfTy` from the type, and the **ivar spine** from it too (`closSpine σ`), because
      judging the body against the *caller's* spine would read the caller's instance variables
      out of a body that belongs to a different object.

      The body judged is `bodyResult c.body`, which differs from `c.body` only for a body
      that is exactly `return e` — see there for why that is a function on the syntax rather
      than a rule for `.ret`.

      **No assumption table**, so a recursive lambda exhausts `chk`'s fuel and is rejected —
      the same conservatism `callMethod` has, and the same fix would apply. -/
  | closCall {κ : Ctx} {Γ Γ₁ Γ₂ Γb' : Env} {I I₁ I₂ : Ty} {recv : Expr} {m : String}
      {args : List Expr} {argTys : List Ty} {idx : Nat} {cap σ : Ty} {c : Clos}
      {Γb : Env} {ρ : Ty} :
      (m = "call" ∨ m = "[]") →
      Judge κ Γ I recv (.clos idx cap σ) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      closGet? κ.closures idx = some c →
      paramEnv c.params argTys = some Γb →
      Judge (κ.inClosure σ) (Γb ++ spineToEnv cap) (closSpine σ) (bodyResult c.body) ρ Γb'
        (closSpine σ) →
      capIntact cap (Γb ++ spineToEnv cap) Γb' = true →
      Judge κ Γ I (.send (some recv) m args none) ρ (killAliases Γ₂) I₂
  -- ### Tier 9c — the builtin iterators
  --
  -- Three rules, one per *way a block reaches an iterator*: written out at the call site, or
  -- passed with `&` as a Symbol, or passed with `&` as a callable value. See the `IterSig`
  -- section for the signature table and why it is split in two.
  /-- **`arr.each { |x| … }` and friends — an iterator with a block literal.**

      The block's body is typed **right here**, at the parameter types `iterParams?` gives,
      rather than being turned into a `Ty.clos` and called later (`closCall`). That is the
      whole reason this rule is cheap: the block is syntactically present, so there is no need
      for the whole-program block table, no index, and no captured-environment spine.

      **The body's environment is `Γb ++ blockLocals locs ++ Γ₂`** — parameters, then the
      block's own `|x; y|` locals, then *the enclosing environment as of the end of the
      argument list*. All three layers matter: `envGet?` takes the first match, so a parameter
      shadows a block-local which shadows an outer local, which is Ruby's scoping; and the
      outer environment being there at all is what makes `block-two-params-inject`'s and
      `narrow-in-block`'s closure reads work.

      **`capIntact` over the enclosing environment**, not over a `cap` spine, and it is the
      same soundness premise clink 11 added for `closCall`: a block captures locals **by
      reference**, this rule carries `Γ₂` out unchanged, so a body that retyped an outer local
      would leave the caller believing a stale type. Note the two directions this covers at
      once — a block may run *zero* times (an empty receiver), so the outgoing environment
      cannot be the body's either; requiring the types to be unchanged is what makes carrying
      `Γ₂` right in both cases.

      **The ivar spine may not be retyped either** (`… ρ Γb' I₂`, the incoming spine on both
      sides), for the same reason and by the same argument as `callMethod`'s.

      No `κ.selfTy = none` premise, unlike `closCall`/`callDefBlk`. Those two have it because
      they build a `Ty.clos` whose captured environment is only meaningful at a creation site
      this judgment can describe; here nothing is captured into a type, `κ` is passed through
      unchanged, and so `self` inside the body is the `self` outside it — which is exactly
      Ruby. That is deliberate rather than incidental: it is what lets an iterator appear inside
      a method body (tier 11's `xc-ivar-array-map`). -/
  | iterBlock {κ : Ctx} {Γ Γ₁ Γ₂ Γb Γb' : Env} {I I₁ I₂ : Ty} {recv : Expr}
      {m : String} {args : List Expr} {argTys : List Ty} {ps : List Param}
      {locs : List String} {body : Expr} {elem : Ty} {βs : List Ty} {ρ res : Ty} :
      Judge κ Γ I recv (.arrayOf elem) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      IterSig m elem argTys βs ρ res →
      paramEnv ps βs = some Γb →
      Judge κ (Γb ++ blockLocals locs ++ killAliases Γ₂) I₂ (bodyResult body) ρ Γb' I₂ →
      capIntact (envToSpine Γ₂) (Γb ++ blockLocals locs ++ killAliases Γ₂) Γb' = true →
      Judge κ Γ I (.send (some recv) m args (some (.block ps locs body))) res
        (killAliases Γ₂) I₂
  /-- **`arr.map(&:to_s)` — a Symbol coerced to a block.**

      `Symbol#to_proc` builds a one-parameter callable that *sends that name to its argument*,
      so the block's return type is exactly the result of a send — and this judgment already
      has a table of those. The premise is therefore `PrimSig β s [] ρ`: the same row
      `arr.map { |x| x.to_s }` would use, reached from the other syntax.

      Restricted to a one-parameter iterator (`βs = [β]`), because that is what
      `Symbol#to_proc` produces. `inject(&:+)` is legal Ruby and needs a two-parameter reading
      of the same coercion; no rung writes it, and admitting it would be a second claim about
      `to_proc` rather than a generalisation of this one. -/
  | iterSymPass {κ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty} {recv : Expr}
      {m s : String} {args : List Expr} {argTys : List Ty} {elem β ρ res : Ty} :
      Judge κ Γ I recv (.arrayOf elem) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      IterSig m elem argTys [β] ρ res →
      PrimSig β s [] ρ →
      Judge κ Γ I (.send (some recv) m args (some (.blockpass (some (.sym s))))) res Γ₂ I₂

  /-- **`arr.map(&some_lambda)` — a callable value passed as the block.**

      The `&` expression is typed (it is an ordinary expression — a local read, in
      `block-pass-lambda-variable`), and its type has to be a `Ty.clos`, at which point this is
      `closCall` with the argument list supplied by `iterParams?` instead of by a call site.
      Everything about the body's environment and `capIntact` is `closCall`'s, unchanged: a
      value-level callable *did* capture into a spine, so here the spine is what is protected,
      not the enclosing environment.

      Note the `&` expression is typed **after** the receiver and the arguments, which is
      Ruby's order, and its outgoing states thread into the body. -/
  | iterClosPass {κ : Ctx} {Γ Γ₁ Γ₂ Γ₃ Γb Γb' : Env} {I I₁ I₂ I₃ : Ty} {recv pe : Expr}
      {m : String} {args : List Expr} {argTys : List Ty} {idx : Nat} {cap σ : Ty}
      {c : Clos} {elem β ρ res : Ty} :
      Judge κ Γ I recv (.arrayOf elem) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      Judge κ Γ₂ I₂ pe (.clos idx cap σ) Γ₃ I₃ →
      IterSig m elem argTys [β] ρ res →
      closGet? κ.closures idx = some c →
      paramEnv c.params [β] = some Γb →
      Judge (κ.inClosure σ) (Γb ++ spineToEnv cap) (closSpine σ) (bodyResult c.body) ρ Γb'
        (closSpine σ) →
      capIntact cap (Γb ++ spineToEnv cap) Γb' = true →
      Judge κ Γ I (.send (some recv) m args (some (.blockpass (some pe)))) res
        (killAliases Γ₃) I₃
  -- ### Tier 9b — a block reaching a method
  --
  -- Four rules. `callDefBlk` is the call site that carries a block; `yieldExpr` is the one
  -- way to reach it that needs nothing named; `vcallAsm`/`vcallDef` close the bare-name
  -- conservatism `bareName` has carried since tier 6, which `lambda-explicit-return` is the
  -- first rung to trip over.
  /-- **A call to a top-level method that passes a block**: `twice { |x| x * 10 }`,
      `run { |x| x + 1 }`.

      Two things happen to the block, and Ruby does both: it is put in `Ctx.blockTy` so
      `yield` can reach it, **and** it is offered to `paramEnvB` so a `&b` parameter can name
      it. `yield-arith` uses the first, `block-param-ampersand` the second, and a method could
      use both.

      The block's type is a `Ty.clos` built exactly as `lambdaLit` builds one — same index
      into the same whole-program table, same captured environment — because a block literal
      and a lambda literal *are* the same node (`Expr.block`). The only difference is where
      the node sits.

      **No assumption table here**, unlike `callDef`: a method that recurses while passing a
      block exhausts `chk`'s fuel and is rejected. Nothing in the corpus does, and the
      two-pass machinery would have to be keyed by the block type as well as the argument
      types.

      **The captured environment is `Γ'`, the environment the *arguments* left behind** — not
      `Γ`, which is what this rule said until tier 11. A block captures locals by reference and
      the arguments are evaluated before the block ever runs, so an argument that rebinds a
      local at a new type must be visible inside the block: `x = 1; t(x = "s") { x + 1 }` would
      otherwise capture `x : Int` and certify a program that raises. No rung has an argument
      with an effect, so this was a latent bug rather than a wrong number — recorded because
      the corrected version is what the three tier-11 block-carrying rules below copy.

      `κ.selfTy = none` is kept, and after tier 11 it is doing a *different* job from the one
      `lambdaLit` used it for: not protecting the block (`Ty.clos` now records its creation
      `self`, and this rule records it too) but keeping this rule **disjoint from
      implicit-self dispatch**. Inside a method body a bare `foo { … }` resolves against the
      object, not the top-level `defs` table, which is `selfCallBlk`'s job. -/
  | callDefBlk {κ : Ctx} {Γ Γ' Γb Γb' : Env} {I I' : Ty} {m : String}
      {args : List Expr} {argTys : List Ty} {ps : List Param} {body : Expr}
      {idx : Nat} {d : Defn} {ρ : Ty} :
      κ.selfTy = none →
      JudgeAll κ Γ I args argTys Γ' I' →
      closIdx? κ.closures ps body = some idx →
      defGet? κ.defs m = some d →
      paramEnvB (some (.clos idx (envToSpine Γ') (κ.selfTy.getD .never))) d.params argTys
        = some Γb →
      Judge { κ with blockTy := some (.clos idx (envToSpine Γ') (κ.selfTy.getD .never)) }
        Γb .ivar0 d.body ρ Γb' .ivar0 →
      Judge κ Γ I (.send none m args (some (.block ps [] body))) ρ (killAliases Γ') I'
  -- ### Tier 11 — a block reaching a *method of an object*
  --
  -- Three rules, and no new idea in any of them: each is its block-less twin
  -- (`callMethod`/`callSMethod`/`selfCall`) with `callDefBlk`'s two extra moves — build the
  -- block's `Ty.clos` and put it in **both** `blockTy` (for `yield`) and `paramEnvB` (for a
  -- `&b` parameter). They exist because tier 9 wrote the block-carrying rule only for the
  -- top-level `defs` table, so `A.new.a { … }` had no rule and nothing in the corpus noticed
  -- until a human wrote ordinary Ruby (`implementation-notes.md` clink 11).
  --
  -- The block's creation `self` is `κ.selfTy` — the **call site's**, which is what
  -- `Ty.clos`'s third field is for and what makes `xc-inherit-implicit-block` (a block
  -- written inside `Child#show`) work.
  /-- **`obj.m(args) { |x| … }`** — an instance method called with a block.
      `callMethod` plus the block. -/
  | callMethodBlk {κ : Ctx} {Γ Γ₁ Γ₂ Γb Γb' : Env} {I I₁ I₂ Iself : Ty} {recv : Expr}
      {m : String} {args : List Expr} {argTys : List Ty} {n dc : String} {d : Defn}
      {ps : List Param} {body : Expr} {idx : Nat} {ρ : Ty} :
      Judge κ Γ I recv (.inst n Iself) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      closIdx? κ.closures ps body = some idx →
      mroGet? κ.classes n m = some (dc, d) →
      paramEnvB (some (.clos idx (envToSpine Γ₂) (κ.selfTy.getD .never))) d.params argTys
        = some Γb →
      Judge { (κ.inMethod (.inst n Iself) dc m) with
              blockTy := some (.clos idx (envToSpine Γ₂) (κ.selfTy.getD .never)) }
        Γb Iself d.body ρ Γb' Iself →
      Judge κ Γ I (.send (some recv) m args (some (.block ps [] body))) ρ
        (killAliases Γ₂) I₂
  /-- **`C.m(args) { |x| … }`** — a singleton method (or a module function) called with a
      block. `callSMethod` plus the block; the spine is `.ivar0` on both sides, because a
      class object has no instance variables this checker models. -/
  | callSMethodBlk {κ : Ctx} {Γ Γ₁ Γ₂ Γb Γb' : Env} {I I₁ I₂ : Ty} {recv : Expr}
      {m : String} {args : List Expr} {argTys : List Ty} {n dc : String} {d : Defn}
      {ps : List Param} {body : Expr} {idx : Nat} {ρ : Ty} :
      Judge κ Γ I recv (.clsOf n) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      closIdx? κ.closures ps body = some idx →
      smroGet? κ.classes n m = some (dc, d) →
      paramEnvB (some (.clos idx (envToSpine Γ₂) (κ.selfTy.getD .never))) d.params argTys
        = some Γb →
      Judge { (κ.inMethod (.clsOf n) dc m) with
              blockTy := some (.clos idx (envToSpine Γ₂) (κ.selfTy.getD .never)) }
        Γb .ivar0 d.body ρ Γb' .ivar0 →
      Judge κ Γ I (.send (some recv) m args (some (.block ps [] body))) ρ
        (killAliases Γ₂) I₂
  /-- **`m(args) { |x| … }` inside a method body** — implicit-self dispatch carrying a block.
      `selfCall` plus the block, plus arguments (which `selfCall` itself does not have, because
      a *bare* name is the zero-argument form and a `vcall` has nowhere to put a block).

      This is `xc-inherit-implicit-block`'s rule, and the dispatch is the interesting part
      rather than the block: `wrap { 7 }` inside `Child#show` finds `Base#wrap` by the ordinary
      `mroGet?` walk, and the block — written inside `Child#show`, so with creation `self`
      `.inst "Child" …` — travels down to a `yield` in the parent's body. Two tiers'
      mechanisms meeting with nothing added to either. -/
  | selfCallBlk {κ : Ctx} {Γ Γ' Γb Γb' : Env} {I I' Iself : Ty} {m : String}
      {args : List Expr} {argTys : List Ty} {n dc : String} {d : Defn}
      {ps : List Param} {body : Expr} {idx : Nat} {ρ : Ty} :
      κ.selfTy = some (.inst n Iself) →
      JudgeAll κ Γ I args argTys Γ' I' →
      closIdx? κ.closures ps body = some idx →
      mroGet? κ.classes n m = some (dc, d) →
      paramEnvB (some (.clos idx (envToSpine Γ') (κ.selfTy.getD .never))) d.params argTys
        = some Γb →
      Judge { (κ.inMethod (.inst n Iself) dc m) with
              blockTy := some (.clos idx (envToSpine Γ') (κ.selfTy.getD .never)) }
        Γb Iself d.body ρ Γb' Iself →
      Judge κ Γ I (.send none m args (some (.block ps [] body))) ρ (killAliases Γ') I'
  /-- **`yield args`** — invoke the block the enclosing method was called with.

      `Ctx.blockTy` supplies it, so this rule is only available inside a body entered through
      `callDefBlk`; a `yield` in a method called without a block raises `LocalJumpError`, and
      with `blockTy = none` there is simply no derivation. The rest is `closCall`'s body: the
      block's parameters bound to `yield`'s argument types, then its captured locals.

      Note that a method can `yield` more than once at different argument types
      (`yield-arith`'s `yield(1) + yield(2)` happens not to), and each `yield` is checked
      independently — the same per-call-site instantiation as everywhere else.

      The body is judged in `κ.inClosure σ` at `closSpine σ` (tier 11), for exactly
      `closCall`'s reasons: the block belongs to whoever *wrote* it, not to the method that
      yields to it. `κ.selfTy = none` is gone with the same change — the yielding method may
      now be an instance method, which is what `xc-class-yield-ivar`/`xc-module-yield`/
      `xc-inherit-implicit-block` need. -/
  | yieldExpr {κ : Ctx} {Γ Γ' Γb' : Env} {I I' : Ty} {args : List Expr}
      {argTys : List Ty} {idx : Nat} {cap σ : Ty} {c : Clos} {Γb : Env} {ρ : Ty} :
      κ.blockTy = some (.clos idx cap σ) →
      JudgeAll κ Γ I args argTys Γ' I' →
      closGet? κ.closures idx = some c →
      paramEnvB none c.params argTys = some Γb →
      Judge (κ.inClosure σ) (Γb ++ spineToEnv cap) (closSpine σ) (bodyResult c.body) ρ Γb'
        (closSpine σ) →
      capIntact cap (Γb ++ spineToEnv cap) Γb' = true →
      Judge κ Γ I (.yield' args) ρ (killAliases Γ') I'
  /-- A **bare name that is a top-level method**, with the instantiation assumed. `vcallAsm`
      is to `callAsm` what `vcallDef` is to `callDef`; see `AsmTable`. -/
  | vcallAsm {κ : Ctx} {Γ : Env} {I : Ty} {m : String} {ρ : Ty} :
      κ.selfTy = none → asmGet? κ.asms m [] = some ρ →
      Judge κ Γ I (.vcall m) ρ Γ I
  /-- A **bare name that is a top-level method**: `def apply_twice; …; end; apply_twice`.

      `bareName`'s docstring has recorded this gap since tier 6 — "there is no rule for a
      top-level `vcall` that *does* name a defined method, because the desugarer emits a
      `vcall` rather than an argument-less `send`" — and `lambda-explicit-return` is the first
      rung to need it. Mechanically it is `callDef` at zero arguments, assume-then-verify and
      all, which is why `vcallAsm` comes with it.

      This does not overlap `bareName`, which requires `defGet? κ.defs m = none`, nor
      `selfCall`/`selfSCall`, which require a `self`. -/
  | vcallDef {κ : Ctx} {Γ Γb Γb' : Env} {I : Ty} {m : String} {d : Defn} {ρ : Ty} :
      κ.selfTy = none → defGet? κ.defs m = some d → paramEnv d.params [] = some Γb →
      Judge { κ with asms := ⟨m, [], ρ⟩ :: κ.asms } Γb .ivar0 d.body ρ Γb' .ivar0 →
      Judge κ Γ I (.vcall m) ρ Γ I
  /-- `self`. Its type is whatever the context says, which inside a method body is
      `.inst n Iself` — not merely "a `Point`" but *this* `Point`, ivars and all. That is
      what makes `Point.new(7).myself.getX` type: `myself` returns a value whose type still
      records `@x : Integer` (rung `class-self-returning-method`). At top level `κ.selfTy`
      is `none` and there is no rule. -/
  | selfExpr {κ : Ctx} {Γ : Env} {I : Ty} {σ : Ty} :
      κ.selfTy = some σ → Judge κ Γ I .self' σ Γ I
  /-- Reading an instance variable. `(ivarGet? I x).getD .nilT` — and the defaulting is the
      rule's content, not a fallback: **reading an instance variable that was never assigned
      yields `nil` in Ruby**; it does not raise. So `class Box; def reveal; @secret; end;
      end; Box.new.reveal` is `nil`, and that is rung `class-ivar-lazy-nil`.

      The default is sound only because the spine is *complete* — every ivar the object has
      ever been given a value for appears in it — which is what `callMethod`'s
      no-retyping premise buys. Without that premise this rule would be the place the
      unsoundness surfaced. -/
  | ivarRead {κ : Ctx} {Γ : Env} {I : Ty} {x : String} :
      Judge κ Γ I (.var .ivar x) ((ivarGet? I x).getD .nilT) Γ I
  /-- Assigning an instance variable. Value is the right-hand side's, exactly as for a
      local; effect is on the spine rather than on `Γ`, and lands in `I'` — the spine the
      right-hand side left behind — for the same evaluation-order reason `vasgn` adds to
      `Γ'`. -/
  | ivarAsgn {κ : Ctx} {Γ Γ' : Env} {I I' : Ty} {x : String} {e : Expr} {τ : Ty} :
      Judge κ Γ I e τ Γ' I' → Judge κ Γ I (.vasgn .ivar x e) τ Γ' (ivarSet I' x τ)
  /-- An explicit-receiver, block-less `send` whose receiver and arguments type, and
      whose resulting shape has a justified `PrimSig`.

      Three restrictions are each doing work: `some recv` (an implicit-self send has
      nobody to dispatch on in this fragment), `blk = none` (a block would need
      `Expr.block` typing, tier ≥ 9), and `PrimSig` matching the *synthesized* argument
      types exactly (no subsumption — see the module docstring). -/
  | prim {κ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty} {recv : Expr} {m : String}
      {args : List Expr} {σ τ : Ty} {argTys : List Ty} :
      Judge κ Γ I recv σ Γ₁ I₁ → JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      PrimSig σ m argTys τ →
      Judge κ Γ I (.send (some recv) m args none) τ Γ₂ I₂
  /-- **`recv.is_a?(C)` → `Bool`** (tier 12).

      Not a `PrimSig` row, and the reason is the interesting part: `PrimSig` is a relation on
      `(receiver type, name, argument types, result)` with no access to the class table, and
      the *safety* of `is_a?` depends on the table — a program-declared class may override
      it. `isADispatchOk` is that check, and it needs `κ.classes`, so the rule has to live
      here. (`nil?` stayed a `PrimSig` row only because `NilQSafe` sidesteps the table by
      refusing `.inst` altogether, which `is_a?` cannot afford to do.)

      **The result is always `.bool`, whatever the answer.** This rule does not compute
      whether the receiver *is* a `C`; `isAAnswer` does that, and it is consulted by
      `narrowEnvs`, in the branch that learns from it. Keeping the two apart is what lets
      `x.is_a?(C)` be an ordinary expression — usable as a value, storable in a local — while
      only an `if` gets to draw a conclusion from it.

      **The argument is required to have a class-object type, not to be a constant.** So
      `x.is_a?(Integer)` and `x.is_a?(Dog)` both type (via `constBuiltin`/`constCls`), and so
      would `k = Dog; x.is_a?(k)` if a rule ever typed that — it just would not *narrow*, for
      lack of a class name in the syntax (see `NarrowCond.isAQuery`). The `.clsOf` requirement
      is what keeps `x.is_a?(5)` out: `is_a?` raises `TypeError` on a non-Module argument,
      which is inside the family. -/
  | isAQuery {κ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty} {recv : Expr}
      {args : List Expr} {σ : Ty} {cn : String} :
      Judge κ Γ I recv σ Γ₁ I₁ → JudgeAll κ Γ₁ I₁ args [.clsOf cn] Γ₂ I₂ →
      isADispatchOk κ.classes σ = true →
      Judge κ Γ I (.send (some recv) "is_a?" args none) .bool Γ₂ I₂
  /-- **`C === v` → `Bool`** (tier 12) — `Module#===`, which is what `case v when C` desugars
      to.

      Not `isAQuery` with the arguments swapped, even though the *answer* is the same: this is a
      different method on a different receiver, and it has a different guard. `Module#===` is
      implemented directly as the ancestor test — it does **not** go through `obj.is_a?` — so a
      user-written `is_a?` cannot affect it, and `isADispatchOk` is not needed. What *can*
      affect it is a `def self.===` on the class object, which is what `smroGet? … = none`
      excludes.

      The argument's type is unconstrained: `Module#===` is total on every object and never
      raises. As with `isAQuery`, the rule computes nothing about the *answer*; `isAAnswer` does
      that, and only `narrowEnvs` consults it. -/
  | caseEqQuery {κ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty} {recv : Expr}
      {args : List Expr} {cn : String} {σ : Ty} :
      Judge κ Γ I recv (.clsOf cn) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args [σ] Γ₂ I₂ →
      smroGet? κ.classes cn "===" = none →
      Judge κ Γ I (.send (some recv) "===" args none) .bool Γ₂ I₂

/-- Pointwise `Judge` over an argument list, with matching length by construction and
both states threaded left to right (Ruby's argument evaluation order). -/
inductive JudgeAll : Ctx → Env → Ty → List Expr → List Ty → Env → Ty → Prop
  | nil {κ : Ctx} {Γ : Env} {I : Ty} : JudgeAll κ Γ I [] [] Γ I
  | cons {κ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty} {e : Expr} {es : List Expr}
      {τ : Ty} {τs : List Ty} :
      Judge κ Γ I e τ Γ₁ I₁ → JudgeAll κ Γ₁ I₁ es τs Γ₂ I₂ →
      JudgeAll κ Γ I (e :: es) (τ :: τs) Γ₂ I₂

/-- Key-then-value `Judge` over a hash literal's pairs, threading both states in
Ruby's evaluation order. No types appear in the conclusion: this relation exists purely
to require that each key and each value *has* one (see `Judge.hashLit`). -/
inductive JudgePairs : Ctx → Env → Ty → List (Expr × Expr) → Env → Ty → Prop
  | nil {κ : Ctx} {Γ : Env} {I : Ty} : JudgePairs κ Γ I [] Γ I
  | cons {κ : Ctx} {Γ Γ₁ Γ₂ Γ₃ : Env} {I I₁ I₂ I₃ : Ty} {k v : Expr}
      {ps : List (Expr × Expr)} {σ ν : Ty} :
      Judge κ Γ I k σ Γ₁ I₁ → Judge κ Γ₁ I₁ v ν Γ₂ I₂ → JudgePairs κ Γ₂ I₂ ps Γ₃ I₃ →
      JudgePairs κ Γ I ((k, v) :: ps) Γ₃ I₃

/-- A non-empty statement sequence. The result type is the last statement's; every
earlier statement must still type (a statement nobody reads can still be type-stuck),
and each one's outgoing state is the next one's incoming.

**Also where the syntax tables grow.** `cons` continues with `κ.afterStmt e`, so a
top-level `def` or `class` becomes visible to the statements that follow it and to no
earlier one. This is the only rule in the file that changes `κ.defs`/`κ.classes`, and it is
why `foo(); def foo; end` has no derivation. -/
inductive JudgeSeq : Ctx → Env → Ty → List Expr → Ty → Env → Ty → Prop
  | last {κ : Ctx} {Γ Γ' : Env} {I I' : Ty} {e : Expr} {τ : Ty} :
      Judge κ Γ I e τ Γ' I' → JudgeSeq κ Γ I [e] τ Γ' I'
  | cons {κ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty} {e e' : Expr}
      {es : List Expr} {σ τ : Ty} :
      Judge κ Γ I e σ Γ₁ I₁ → JudgeSeq (κ.afterStmt e) Γ₁ I₁ (e' :: es) τ Γ₂ I₂ →
      JudgeSeq κ Γ I (e :: e' :: es) τ Γ₂ I₂
  /-- **The guard clause: `return e if c`, followed by more statements** (tier 12).

      Ruby's most common narrowing idiom, and the only one that narrows by *elimination of a
      branch that leaves* rather than by being inside a branch:

      ```ruby
      x = a[0]
      return 0 if x.nil?      # <- this statement
      x + 1                   # <- x is not nil here, and no `if` encloses this line
      ```

      **Why this is a `JudgeSeq` rule and not a rule for `.ret`.** `.ret` has no rule of its
      own anywhere in this judgment, deliberately: giving `.ret e` the type of `e` makes
      `def f; return "a"; 2; end` validate at `Int` (`bodyResult`'s docstring), and giving it
      `.never` fails the same way, because `JudgeSeq` takes the *last* statement's type either
      way. Both fixes need the sequence to know that a statement did not fall through — which
      is information about the sequence, so the rule belongs to the sequence. Stated at this
      one syntactic shape (`.if' c (.ret (some e)) none` in non-final position) it needs no
      general return-type accumulator, and everything else about `.ret` stays underivable.

      **What the rule says**, premise by premise:

      - the condition types (evaluating it can itself be type-stuck);
      - the returned expression types **in the then-branch's narrowed environment**, because
        that is where the guard fired;
      - the rest of the sequence types in the **else**-branch's narrowed environment —
        `(narrowEnvs …).2` — which is the entire point: the code after a guard runs only on
        the path the guard let through;
      - and the sequence's type is `joinT ρ τ`, the join of *what the guard returns* with what
        the rest returns. This is the one place a value leaves a sequence from somewhere other
        than its last statement.

      `κ` rather than `κ.afterStmt` for the rest, because `extendClasses`/`extendDefs` are
      visibly the identity on an `.if'`: a guard declares nothing.

      `Ir = Ic` requires the returned expression to leave the ivar spine alone. Not a
      restriction any rung feels (a guard returns a constant or a local), and it is needed
      because the spine this rule reports is the *rest*'s: an ivar written on the returning
      path would be invisible to the caller's `Iout = Iself` check. -/
  | guard {κ : Ctx} {Γ Γc Γr Γ' : Env} {I Ic Ir I' : Ty} {c e : Expr}
      {rest : List Expr} {σ ρ τ : Ty} :
      Judge κ Γ I c σ Γc Ic →
      Judge κ (narrowEnvs κ.classes c Γc).1 (narrowSpine κ.classes c Ic).1 e ρ Γr Ir →
      Ir = (narrowSpine κ.classes c Ic).1 →
      JudgeSeq κ (narrowEnvs κ.classes c Γc).2 (narrowSpine κ.classes c Ic).2 rest τ Γ' I' →
      JudgeSeq κ Γ I (.if' c (.ret (some e)) none :: rest) (joinT ρ τ) Γ' I'

end

end Ratchet
