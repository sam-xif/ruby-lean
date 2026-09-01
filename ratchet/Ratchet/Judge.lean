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
      `smethods`, misses, and is rejected — which is what Ruby does too. -/
  isModule : Bool

abbrev CTable := List Cls

def clsGet? (C : CTable) (n : String) : Option Cls := C.find? (·.name == n)

/-- One member of a class body that this checker can read. -/
inductive ClsMember where
  | inst (d : Defn)
  | sing (d : Defn)

def clsMember? : Expr → Option ClsMember
  | .def' n ps b => some (.inst ⟨n, ps, b⟩)
  -- `def self.m` is the only `defs` receiver read: `def obj.m` for some other object is a
  -- singleton method on *that* object, which this checker has no way to record.
  | .defs .self' n ps b => some (.sing ⟨n, ps, b⟩)
  | _ => none

def splitMembers : List ClsMember → List Defn × List Defn
  | [] => ([], [])
  | .inst d :: ms => let (i, s) := splitMembers ms; (d :: i, s)
  | .sing d :: ms => let (i, s) := splitMembers ms; (i, d :: s)

/-- A class body's instance and singleton methods, or `none` if the body contains anything
this checker cannot read.

**That `none` is doing two jobs at once**, which is why the restriction sits in one place.
It is what makes the body safe to *evaluate* unchecked — a `def`/`defs` statement never runs
its body, and `nil` is `nil`, so a body made only of those cannot be type-stuck — and it is
what makes the class readable into `CTable`. A body with an ivar assignment at class level, a
nested class, or anything executable is not typed at all: conservative in the direction that
costs rungs rather than soundness, and it is the shape every tier-7 rung has. -/
def classMethods? : Expr → Option (List Defn × List Defn)
  | .nil => some ([], [])
  | .seq es => (es.mapM clsMember?).map splitMembers
  | e => (clsMember? e).map (fun m => splitMembers [m])

/-! ### Method lookup, up the chain

`defGet?` finds a method declared *on* a class. `mroGet?` finds the one dispatch would
actually run, walking `super?`, and returns **which class it was found in** as well as the
method — because `super` needs the definition site, not the receiver's class (see
`Judge.superCall`). -/

/-- The bounded walk. `k` is a depth budget, not a natural part of the algorithm: `CTable` is
data, so nothing stops it describing a cycle (`class A < B` and `class B < A` cannot both be
declared in Ruby, but the table does not know that). Exhausting the budget answers `none`,
which — like `chk`'s fuel — can only cost completeness. -/
def lookupUp (C : CTable) (sing : Bool) : Nat → String → String → Option (String × Defn)
  | 0, _, _ => none
  | k + 1, n, m =>
    match clsGet? C n with
    | none => none
    | some c =>
      match defGet? (if sing then c.smethods else c.methods) m with
      | some d => some (n, d)
      | none =>
        match c.super? with
        | none => none
        | some sn => lookupUp C sing k sn m

/-- Instance-method lookup from class `n`. The budget is the table's own length: a chain
longer than that must have revisited a class. -/
def mroGet? (C : CTable) (n m : String) : Option (String × Defn) :=
  lookupUp C false C.length n m

/-- Singleton-method lookup. Ruby inherits class methods down the chain too, so this is the
same walk over the other table. -/
def smroGet? (C : CTable) (n m : String) : Option (String × Defn) :=
  lookupUp C true C.length n m

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

def extendClasses (C : CTable) : Expr → CTable
  | .class' n sup body =>
    match classMethods? body with
    | some (ms, sms) =>
      match sup with
      | none => ⟨n, none, ms, sms, false⟩ :: C
      | some (.const sn) => ⟨n, some sn, ms, sms, false⟩ :: C
      -- A superclass expression that is not a bare constant (`class C < foo()`) is not
      -- read, so the class does not enter the table and nothing using it is typed.
      | some _ => C
    | none => C
  -- Tier 8. A module is a `Cls` with no superclass and the module flag set; the body is read
  -- by the same `classMethods?`, so `def self.foo` lands in `smethods` and `M.foo` is
  -- `callSMethod` with nothing added.
  | .module' n body =>
    match classMethods? body with
    | some (ms, sms) => ⟨n, none, ms, sms, true⟩ :: C
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
  /-- The type of `self`, or `none` at top level.

      `none` rather than "the type of `main`" because this judgment has no rule that needs
      it: at top level, `self'` is not typed and an implicit-self send goes to the `defs`
      table. Inside a method body it is `some (.inst c ivars)`, which is what makes
      `class-self-returning-method` work — `self` there is not merely "a `Point`", it is
      *this* `Point`, ivars and all. -/
  selfTy : Option Ty

/-- Entering a method body whose `self` has type `σ`. Only `selfTy` changes: the class and
method tables are the ones in force at the call site, and the assumption table is *kept*,
because a recursive call made from inside a body must still find the assumption discharging
it. The body's *locals* are not in `Ctx` at all — they are the threaded `Env`, and a call
rule supplies `paramEnv`'s fresh one. -/
def Ctx.inMethod (κ : Ctx) (σ : Ty) (dc m : String) : Ctx :=
  { κ with selfTy := some σ, frame := some ⟨dc, m⟩ }

/-- Entering a body whose `self` this judgment declines to type — `initialize` (see
`Judge.newInst`) — but whose *definition site* still has to be recorded, because the body may
call `super`. -/
def Ctx.inCtor (κ : Ctx) (dc m : String) : Ctx := { κ with frame := some ⟨dc, m⟩ }

/-- `κ` after performing statement `e`: both syntax tables grow, nothing else changes. Used
only by `JudgeSeq.cons`, which is the only rule that knows about statement order. -/
def Ctx.afterStmt (κ : Ctx) (e : Expr) : Ctx :=
  { κ with classes := extendClasses κ.classes e, defs := extendDefs κ.defs e }

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
      envGet? Γ x = some τ → Judge κ Γ I (.var .lvar x) τ Γ I
  /-- Assignment. Its *value* is the right-hand side's (Ruby's `x = e` evaluates to `e`),
      and its *effect* is to record that type for `x` in the outgoing environment.

      `envSet` overwrites, so `x = 1; x = true` simply re-types `x`; nothing here demands
      the new type relate to the old one. That is not a weakness of the checker, it is
      what a Ruby local *is* (rung `reassign-different-type`). Note the ordering: the
      right-hand side is typed in `Γ` and may itself assign (`y = (x = 1) + 1`), so the
      binding is added to `Γ'`, the environment the RHS left behind — not to `Γ`. -/
  | vasgn {κ : Ctx} {Γ Γ' : Env} {I I' : Ty} {x : String} {e : Expr} {τ : Ty} :
      Judge κ Γ I e τ Γ' I' → Judge κ Γ I (.vasgn .lvar x e) τ (envSet Γ' x τ) I'
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

      **The ivar spine is *not* joined; the two branches must agree on it.** `I₁ = I₂` is a
      premise, not a join, and the difference from the locals is deliberate: a spine is not
      just state, it is part of the *type* of `self` (see `Ty.inst`), and there is no
      pointwise widening of it that keeps that type honest. A branch that assigns an
      instance variable at a new type is therefore rejected rather than widened. No rung
      needs the precision, and the conservatism is in the safe direction. -/
  | if' {κ : Ctx} {Γ Γc Γ₁ Γ₂ : Env} {I Ic I₁ I₂ : Ty} {c t e : Expr}
      {σ τ₁ τ₂ : Ty} :
      Judge κ Γ I c σ Γc Ic → Judge κ Γc Ic t τ₁ Γ₁ I₁ → Judge κ Γc Ic e τ₂ Γ₂ I₂ →
      I₁ = I₂ →
      Judge κ Γ I (.if' c t (some e)) (joinT τ₁ τ₂) (joinEnv Γ₁ Γ₂) I₁
  /-- `if c then t end`, with no `else`. Ruby's missing branch evaluates to `nil`, so
      this is the same rule with the else-branch's type fixed at `.nilT` and its
      environment fixed at `Γc` — the state as of the end of the condition.
      `joinT τ .nilT` is `mkNilable τ` (rung `if-no-else`). The absent branch cannot touch
      the ivar spine, so the same agreement premise reads `I₁ = Ic`. -/
  | ifNoElse {κ : Ctx} {Γ Γc Γ₁ : Env} {I Ic I₁ : Ty} {c t : Expr} {σ τ : Ty} :
      Judge κ Γ I c σ Γc Ic → Judge κ Γc Ic t τ Γ₁ I₁ → I₁ = Ic →
      Judge κ Γ I (.if' c t none) (joinT τ .nilT) (joinEnv Γ₁ Γc) Ic
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
      `κ.classes` separately, because only `JudgeSeq` knows statement order. -/
  | classStmt {κ : Ctx} {Γ : Env} {I : Ty} {n : String} {sup : Option Expr}
      {body : Expr} {ms sms : List Defn} :
      classMethods? body = some (ms, sms) →
      Judge κ Γ I (.class' n sup body) .any Γ I
  /-- A constant naming a declared class, as a **class object** — `.clsOf n`, which
      `Ratchet/Ty.lean` distinguishes from `.cls n` (an instance of it) precisely so that
      `Point` and `Point.new` cannot be confused. Only declared classes get a rule: a
      constant this checker has never seen a `class` statement for is not typed, so
      `Undeclared.new` fails here rather than at dispatch. -/
  | constCls {κ : Ctx} {Γ : Env} {I : Ty} {n : String} {c : Cls} :
      clsGet? κ.classes n = some c → Judge κ Γ I (.const n) (.clsOf n) Γ I
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
      Judge (κ.inCtor dc "initialize") Γb .ivar0 d.body ρ Γb' Iout →
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

      **The class it walks up from is the *definition site*, not the receiver's class**, and
      that is why `Ctx.frame` exists. In `class Triangle < Shape; def initialize; super(3);
      end`, the parent to run is the superclass of `Triangle` — the class this running method
      was declared in. `κ.selfTy` names the receiver's class, which for a deeper hierarchy is
      a different and wrong answer, and inside `initialize` it is not even set.

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
      {argTys : List Ty} {fr : Frame} {c : Cls} {sn dc : String} {d : Defn}
      {ρ : Ty} :
      JudgeAll κ Γ I args argTys Γ' I' →
      κ.frame = some fr → clsGet? κ.classes fr.defClass = some c →
      c.super? = some sn → mroGet? κ.classes sn fr.methName = some (dc, d) →
      paramEnv d.params argTys = some Γb →
      Judge { κ with frame := some ⟨dc, fr.methName⟩ } Γb I' d.body ρ Γb' Iout →
      Judge κ Γ I (.super' args none) ρ Γ' Iout
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
      Judge (κ.inCtor dc "initialize") Γb .ivar0 d.body ρ Γb' Iout →
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
      {ms sms : List Defn} :
      classMethods? body = some (ms, sms) →
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
      - **`κ.selfTy = none`.** A closure's body sees the `self` of wherever it was
        *created*, and this rule records the captured *locals* but not the captured `self`.
        Restricting creation to top level (where `selfTy` is `none`) makes the omission
        harmless instead of unsound: a lambda made inside a `Point` method and called inside
        a `Box` method would otherwise have its body checked against the wrong `self`.
        Lifting this means putting `selfTy` in `Ty.clos` beside the captured locals. -/
  | lambdaLit {κ : Ctx} {Γ : Env} {I : Ty} {m : String} {ps : List Param}
      {body : Expr} {idx : Nat} :
      (m = "lambda" ∨ m = "proc") → κ.selfTy = none →
      closIdx? κ.closures ps body = some idx →
      Judge κ Γ I (.send none m [] (some (.block ps [] body))) (.clos idx (envToSpine Γ)) Γ I
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

      The ivar spine goes in and comes back unchanged, for `callMethod`'s reason: a body that
      retyped an instance variable would invalidate the caller's view of it. `κ.selfTy = none`
      again, matching `lambdaLit`.

      **No assumption table**, so a recursive lambda exhausts `chk`'s fuel and is rejected —
      the same conservatism `callMethod` has, and the same fix would apply. -/
  | closCall {κ : Ctx} {Γ Γ₁ Γ₂ Γb' : Env} {I I₁ I₂ : Ty} {recv : Expr} {m : String}
      {args : List Expr} {argTys : List Ty} {idx : Nat} {cap : Ty} {c : Clos}
      {Γb : Env} {ρ : Ty} :
      (m = "call" ∨ m = "[]") → κ.selfTy = none →
      Judge κ Γ I recv (.clos idx cap) Γ₁ I₁ →
      JudgeAll κ Γ₁ I₁ args argTys Γ₂ I₂ →
      closGet? κ.closures idx = some c →
      paramEnv c.params argTys = some Γb →
      Judge κ (Γb ++ spineToEnv cap) I₂ c.body ρ Γb' I₂ →
      Judge κ Γ I (.send (some recv) m args none) ρ Γ₂ I₂
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

end

end Ratchet
