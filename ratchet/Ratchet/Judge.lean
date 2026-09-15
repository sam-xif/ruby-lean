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
  /-- Tier 17b. `Hash#==` compares contents with `==`, and it is total: unequal shapes are
      simply not equal. Added when `.cls "Hash"` stopped being how a hash is typed — without
      it, `h == other` would have *lost* a row it used to have. -/
  | hashOf {k v : Ty} : EqSafe (.hashOf k v)

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
  | hashOf {k v : Ty} : NilQSafe (.hashOf k v)
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

/-- `BuiltinCls`'s names as a list, for the places that need to *decide* it. -/
def builtinClsNames : List String :=
  ["Integer", "Float", "String", "Symbol", "NilClass", "TrueClass", "FalseClass",
   "Array", "Hash"]

/-! ## Exception classes (tier 16b)

`raise` and `rescue` both name a class, and both **raise `TypeError` when the name is not an
exception class** — `raise 5` is "exception class/object expected". So the judgment needs to know
which names those are, and it needs it for two reasons that pull in different directions:

- the builtin ones (`ArgumentError`, `ZeroDivisionError`, …) are not in `CTable` at all, for
  `constBuiltin`'s reason (a `CTable` row carries method tables, and `ctorGet?` would happily
  allocate against them). So they are a **list**, and the list's *completeness* is a
  coverage condition, not a soundness one: a name missing from it makes a `raise` untypeable.
- a user exception (`class Uncomparable < StandardError`) *is* in `CTable`, and what makes it an
  exception is that its superclass chain reaches one of the builtin names. That is a walk, and
  it is fuel-bounded for `nestedClasses`' reason.

`ExcCls` is deliberately **not** folded into `BuiltinCls`: that relation is kept to the classes
`builtinAncestors` can answer `is_a?` for, and an exception name admitted there would produce a
`.clsOf` nobody can answer `is_a?` for. Here that does not matter, because nothing asks. -/
inductive ExcCls : String → Prop
  | standardError : ExcCls "StandardError"
  | runtimeError : ExcCls "RuntimeError"
  | argumentError : ExcCls "ArgumentError"
  | typeError : ExcCls "TypeError"
  | nameError : ExcCls "NameError"
  | noMethodError : ExcCls "NoMethodError"
  | zeroDivisionError : ExcCls "ZeroDivisionError"
  | indexError : ExcCls "IndexError"
  | keyError : ExcCls "KeyError"
  | rangeError : ExcCls "RangeError"
  | ioError : ExcCls "IOError"
  | frozenError : ExcCls "FrozenError"
  | notImplementedError : ExcCls "NotImplementedError"

/-- The decidable side of `ExcCls`, row for row (`excCls?_sound`). -/
def excCls? : String → Bool
  | "StandardError" | "RuntimeError" | "ArgumentError" | "TypeError" | "NameError"
  | "NoMethodError" | "ZeroDivisionError" | "IndexError" | "KeyError" | "RangeError"
  | "IOError" | "FrozenError" | "NotImplementedError" => true
  | _ => false

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
  /-- **`Array#length`** (tier 14b). Total on every array whatever its element type, and the
      element type does not appear in the result — so unlike `Array#[]` there is nothing to be
      careful about. Its receiver is `.arrayOf`, which no user class can be, so it needs no
      override guard for the same reason the arithmetic rows do not. -/
  | arrayLength {τ : Ty} : PrimSig (.arrayOf τ) "length" [] .int
  -- ### Tier 15 — the `String`/`Regexp` rows
  --
  -- Nine rows, and the finding is how *boring* they are: the target's whole string diet is
  -- total `String -> String` and `String -> Bool` methods. Each is total for the argument types
  -- named (`delete_prefix` and `tr` raise `TypeError` on a non-String, which is why the
  -- arguments are not unconstrained), and each has a `.cls "String"` receiver, which is a
  -- builtin — so they are trusted exactly as far as `strAdd` and `strLength` already were.
  /-- `"  x ".strip` — and `downcase`/`upcase`, whose rows are the same shape. -/
  | strStrip : PrimSig (.cls "String") "strip" [] (.cls "String")
  | strDowncase : PrimSig (.cls "String") "downcase" [] (.cls "String")
  | strUpcase : PrimSig (.cls "String") "upcase" [] (.cls "String")
  | strTr : PrimSig (.cls "String") "tr" [.cls "String", .cls "String"] (.cls "String")
  | strDeletePrefix :
      PrimSig (.cls "String") "delete_prefix" [.cls "String"] (.cls "String")
  | strStartsWith : PrimSig (.cls "String") "start_with?" [.cls "String"] .bool
  /-- `"a/b/c".split("/")` — an `Array` of `String`s whatever the separator matches, which is
      the one row here whose *result* type says something the caller can use. -/
  | strSplit : PrimSig (.cls "String") "split" [.cls "String"] (.arrayOf (.cls "String"))
  /-- `s.sub(/re/, "x")` and `gsub`. The two-argument, non-block forms only: `gsub` also takes
      a Hash or a block, and those are different signatures with different results. -/
  | strSub :
      PrimSig (.cls "String") "sub" [.cls "Regexp", .cls "String"] (.cls "String")
  | strGsub :
      PrimSig (.cls "String") "gsub" [.cls "Regexp", .cls "String"] (.cls "String")
  /-- `s.match?(/re/)` → `Bool`. Total, and the *answer* is not computed anywhere: a `Regexp`
      is opaque in this type language (see `Judge.regexpLit`). -/
  | strMatchP : PrimSig (.cls "String") "match?" [.cls "Regexp"] .bool
  /-- **`s.match(/re/)` → `MatchData` or `nil`**, and the `nilable` is the whole point. This is
      the row that makes `regexp-match-captures` and its permanent-negative twin
      `regexp-no-match-unsafe` two readings of one signature: whether `m[1]` is safe depends on
      whether the match succeeded, which is a fact about the pattern and the subject and not
      about their types. So the row answers `nilable` and the two rungs are separated by
      *narrowing*, or not at all. -/
  | strMatch :
      PrimSig (.cls "String") "match" [.cls "Regexp"] (.nilable (.cls "MatchData"))
  /-- **`Integer#__as_string`** — the desugarer's marker for the `to_s` inside a string
      interpolation, not a method anyone writes (see the `str-interpolation` rungs). Total on
      `Integer` and returns a `String`, which is the only thing interpolation needs. -/
  | intAsString : PrimSig .int "__as_string" [] (.cls "String")
  /-- **`===` on a value receiver** (tier 16) — `case t when "pypi"` desugars to
      `"pypi" === t`, so `case/when` over *values* rather than classes is a send whose receiver
      is the `when` clause's literal.

      Guarded by `EqSafe`, exactly as `objEq` is, and for the same reason: `Object#===` is
      `==` unless someone overrode it, and `EqSafe` is precisely the receivers whose method
      table is the builtin one. The three `EqSafe` types where `===` is *not* `==` are all
      still total — `Regexp#===` is a match test and `Range#===` a containment test — so the
      row's `.bool` holds for them too.

      Disjoint from `Judge.caseEqQuery` (`Module#===`) because `.clsOf` is not `EqSafe`; that
      is the case where the receiver is a class object and the answer is an ancestor test, and
      it needs the class table, which `PrimSig` cannot see. -/
  | caseEqPrim {σ τ : Ty} : EqSafe σ → PrimSig σ "===" [τ] .bool
  /-- `"".empty?` (tier 16b) — total, and the rung that wants it is `ctl-rescue`'s
      `raise ArgumentError if s.empty?`. -/
  | strEmptyP : PrimSig (.cls "String") "empty?" [] .bool
  /-- **`e.message`** (tier 16b) — the one row whose *receiver* is guarded by a name predicate
      rather than by a type shape. `.cls n` for an `ExcCls` name is what a `rescue … => e`
      binding produces (see `rescueBind?`), and `Exception#message` is total on one and returns
      a `String`. Without the guard the row would fire for `.cls "String"`, where `message` is a
      `NoMethodError`. -/
  | excMessage {n : String} : ExcCls n → PrimSig (.cls n) "message" [] (.cls "String")
  -- ### Tier 17 — the collection rows
  --
  -- `homebrew/README.md` §2 measures the gap these close over all of Homebrew (6.4% of 113,610
  -- call sites resolve to nothing we have); this is its slice-sized head. Three of the rows
  -- carry a guard on the **element** type rather than the receiver's, which is new: `include?`
  -- and `uniq` call `==`/`hash`/`eql?` on the elements, so an element whose class overrides one
  -- of those could raise. `NilQSafe` is that guard for the third time, and it is the same
  -- question it has always asked — "is this value's method table the builtin one?" — asked one
  -- level down.
  /-- **`xs << x`** (tier 17), and this row is where `arrayOf`'s **invariance** finally becomes
      load-bearing — the obligation tier 5 recorded when it wrote `arrayOf` with one element
      type and no way to add an element.
      
      The argument's type must be *exactly* the receiver's element type. That looks needlessly
      strict and it is what keeps `IterSig.injectEmpty` honest: `arrayOf .never` is read as
      "provably empty" (nothing inhabits `.never`), and this row cannot break that reading,
      because pushing onto an `arrayOf .never` would need an argument of type `.never` and no
      expression has one. So the invariant survives, and it survives *by* the invariance.
      
      The price is `lib-array-push`: `xs = []; xs << 1` starts at `arrayOf .never` and cannot
      grow, because a send does not retype its receiver's binding. Widening it would mean a rule
      that writes to `Env` off a *receiver* expression, which nothing here does. -/
  | arrayPush {τ : Ty} : PrimSig (.arrayOf τ) "<<" [τ] (.arrayOf τ)
  | arrayEmptyP {τ : Ty} : PrimSig (.arrayOf τ) "empty?" [] .bool
  | arrayInclude {τ σ : Ty} : NilQSafe τ → PrimSig (.arrayOf τ) "include?" [σ] .bool
  /-- `["a", "b"].join("/")`. Restricted to `String` elements: `join` calls `to_s` on every
      element, and a user-written `to_s` can do anything. -/
  | arrayJoin :
      PrimSig (.arrayOf (.cls "String")) "join" [.cls "String"] (.cls "String")
  /-- `[1, nil, 2].compact` — the one row whose *result* type is computed by a tier-12
      refinement: `nonNilTy` is exactly what removing the `nil`s does to the element type. -/
  | arrayCompact {τ : Ty} : PrimSig (.arrayOf τ) "compact" [] (.arrayOf (nonNilTy τ))
  | arrayUniq {τ : Ty} : NilQSafe τ → PrimSig (.arrayOf τ) "uniq" [] (.arrayOf τ)
  /-- `xs.first` / `xs.last` — `nilable`, because the array may be empty, and that is the whole
      of §Frontier item G: the slice writes `arr.first` where it *knows* the array is non-empty,
      and `Ty` cannot say so. `lib-array-first-last` is the rung this row does not climb and
      `lib-array-first-nil-unsafe` is the program it correctly rejects. -/
  | arrayFirst {τ : Ty} : PrimSig (.arrayOf τ) "first" [] (mkNilable τ)
  | arrayLast {τ : Ty} : PrimSig (.arrayOf τ) "last" [] (mkNilable τ)
  | intSpaceship : PrimSig .int "<=>" [.int] .int
  /-- `h.key?("a")` — total, and the `NilQSafe` guard is on the *argument* here, because that is
      what `Hash#key?` hashes. Answers `Bool` and nothing about the value behind the key, which
      the bare `.cls "Hash"` could not describe anyway (§Frontier item A). -/
  | hashKeyP {k v σ : Ty} : NilQSafe σ → PrimSig (.hashOf k v) "key?" [σ] .bool
  -- ### Tier 17b — the parameterised `Hash`
  --
  -- Every row's key argument carries a `NilQSafe` guard, because every one of them **hashes**
  -- it, and a user-written `hash`/`eql?` can raise. The *key* parameter of the type is
  -- deliberately not required to match: `h[wrong_type]` is not an error in Ruby, it is `nil`,
  -- and pretending otherwise would reject safe programs (`param-kwrest` reads a symbol-keyed
  -- hash with a String key on purpose).
  /-- `h.fetch(k)` → the value type, **not** a nilable one. A missing key raises `KeyError`,
      which is *outside* the type-stuck family — so if the key is absent execution ends there
      and no claim about the result can be falsified. This is the same argument `NameError`
      gets in tier 13, and it is the reason `fetch` is more useful than `[]` to a checker: the
      one-argument form is total *on the values it returns*. -/
  | hashFetch {k v σ : Ty} : NilQSafe σ → PrimSig (.hashOf k v) "fetch" [σ] v
  /-- `h.fetch(k, d)` → the value type joined with the default's, because either can come
      back. -/
  | hashFetchD {k v σ ρ : Ty} :
      NilQSafe σ → PrimSig (.hashOf k v) "fetch" [σ, ρ] (joinT v ρ)
  | hashLength {k v : Ty} : PrimSig (.hashOf k v) "length" [] .int
  /-- `h.dig(k)` — `[]` under another name for one level, and `nilable` for the same reason. -/
  | hashDig {k v σ : Ty} : NilQSafe σ → PrimSig (.hashOf k v) "dig" [σ] (mkNilable v)
  /-- `h.dig(k1, k2)` on a hash **of hashes** → the inner value or nil. Two levels only: the
      row has to name the nesting depth in the type, so each depth is a row, and the slice
      writes at most two. -/
  | hashDig2 {k v k2 σ σ2 : Ty} :
      NilQSafe σ → NilQSafe σ2 →
      PrimSig (.hashOf k (.hashOf k2 v)) "dig" [σ, σ2] (mkNilable v)
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
  /-- `Hash#[] (anything) → nilable val` (rung `hash-index`), and **the row this whole ladder
      spent longest unable to write usefully**.

      Until tier 17b it read `PrimSig (.cls "Hash") "[]" [τ] .any` — sound and inert, since
      there was no `hashOf` constructor to read a value type back off, so `{"a"=>1}["a"] + 1`
      was safe Ruby no rule could type. `Ty.hashOf` fixes that and the row's shape barely
      changes.

      **The key argument is not required to match the key parameter.** A missing key answers
      `nil` rather than raising (`{"a"=>1}["z"]`, `{"a"=>1}[[1,2]]`), so there is no key type
      to exclude — and requiring a match would reject safe programs (`param-kwrest` reads a
      symbol-keyed hash with a `String` key, deliberately). What the argument *does* carry is
      `NilQSafe`, because `[]` hashes it.

      **`nilable`, for `Array#[]`'s reason**: the checker cannot know the key is present. Its
      total sibling is `fetch`, which is more useful precisely because a missing key there
      raises `KeyError` — outside the type-stuck family. -/
  | hashIndex {k v σ : Ty} : NilQSafe σ → PrimSig (.hashOf k v) "[]" [σ] (mkNilable v)
  -- ### Tier 12's row
  /-- `recv.nil? () → Bool` for a `NilQSafe` receiver (rung `narrow-nilable-nil-check`).

      Total and never coercing: `Object#nil?` returns `false` for every object,
      `NilClass#nil?` returns `true`, and neither takes an argument or can raise. The
      entire content of this row is therefore in `NilQSafe`, which says which receivers
      this ladder is willing to claim reach one of those two definitions rather than a
      user-written override. -/
  | nilQuery {σ : Ty} : NilQSafe σ → PrimSig σ "nil?" [] .bool
  /-- **`Object#freeze` — the identity** (tier 13). Every frozen constant table in the target
      is written `= {...}.freeze`, and `freeze` returns the receiver itself, so the row is
      receiver-polymorphic in exactly the way `objEq` is argument-polymorphic.

      The guard is `NilQSafe` again, and for the same reason it exists there: a user-defined
      `def freeze` on an instance would be dispatched to instead, so `.inst` is refused
      outright. Reusing the predicate rather than writing a `FreezeSafe` twin is a deliberate
      call — the two conditions are the same condition ("this receiver's method table is the
      builtin one"), and a second copy would be a second thing to keep true. -/
  | freezeId {σ : Ty} : NilQSafe σ → PrimSig σ "freeze" [] σ

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

/-! ### A body that declares (`found-issues.md` §F3)

`Ctx` describes *declarations* — `defs`, `classes`, `consts` — and every rule that types a
**call** concludes at the same `κ` it started from. That is a promise that running the body
leaves those tables describing the heap, and a body containing a `def` breaks it: the `def`
executes, `Heap.defineMethod` **replaces**, and the caller's table now names a method the
heap no longer has. `def bar; 1; end; def foo; def bar; "s"; end; 1; end; foo; bar + 1` was
certified `Integer` and raises `TypeError` in CRuby *and* in the model.

The fix is at the **lookup**, not at the rules, and that is worth a sentence because it is what
made it a five-line change instead of a premise on twenty rules: a rule can only type a call by
first *fetching the body* — `defGet?` for a top-level method, `defGet? c.methods` for an
instance method (the same function, `mroGet?` included), `closGet?` for a Proc or a block a
method may `yield`. Filter there and every call rule inherits the guard, with no premise added,
no derivation term moved and no `chk_sound` case touched.

What it costs is precision, exactly once: a method whose body declares becomes **uncallable by
this checker** rather than callable-and-wrong. Nothing else can reach it either — typing a body
requires a rule for every statement in it, so a method that merely *calls* the unrecordable one
is rejected in turn, and `define_method` has no rule at all.

The alternative, recorded because it is where this should end up: thread the context through the
judgment (`Judge κ Γ I e τ Γ' I' κ'`), which fixes this *and* `Judge.defStmt`'s false semantic
obligation (`Denote/Sem/notes.md` §The sixth stall point). That is a change to every derivation
on file and wants its own clink. -/

mutual

/-- Does this expression contain no **declaration** — no `def`, no `class`/`module`/`sclass`, no
constant assignment, no `undef`/`alias`?

Written as its own structural recursion (mutual with the list and pair walkers) rather than with
`List.all`, for `collectBlocks`' reason and `exprEq`'s: a helper outside the nested-inductive
bundle pushes the group onto well-founded recursion, and then it stops reducing in the kernel —
which every `rfl`-discharged `defGet? … = some d` premise in `Rungs.lean` depends on.

Parameters are **not** walked, and that is a known gap rather than an omission: a default
expression (`def f(x = (def bar; end; 1))`) is evaluated in the callee frame and could declare.
No rung writes one, walking `Param` would put a third inductive in the recursion bundle, and the
gap is recorded here so the fix has somewhere to start. -/
def declFree : Expr → Bool
  -- the declarations themselves
  | .def' .. | .defs .. | .casgn .. | .cpathAsgn .. => false
  | .class' .. | .module' .. | .scopedClass .. | .scopedModule .. | .sclass .. => false
  | .undef .. | .alias' .. => false
  -- containers
  | .vasgn _ _ e | .splat (some e) | .ret (some e) | .brk (some e) | .nxt (some e)
  | .blockpass (some e) | .cpath (some e) _ | .defined e => declFree e
  | .send recv _ args blk =>
    (match recv with | some r => declFree r | none => true) &&
    declFreeAll args &&
    (match blk with | some b => declFree b | none => true)
  | .block _ _ body => declFree body
  | .seq es | .array es | .yield' es => declFreeAll es
  | .hash ps => declFreePairs ps
  | .kwargs entries => declFreeKw entries
  | .if' c t e =>
    declFree c && declFree t && (match e with | some x => declFree x | none => true)
  | .while' c body => declFree c && declFree body
  | .dowhile body cond => declFree body && declFree cond
  | .for' _ coll body => declFree coll && declFree body
  | .begin' body rescues els ens =>
    declFree body && declFreeRescues rescues &&
    (match els with | some x => declFree x | none => true) &&
    (match ens with | some x => declFree x | none => true)
  | .super' args blk =>
    declFreeAll args && (match blk with | some b => declFree b | none => true)
  | .zsuper blk => (match blk with | some b => declFree b | none => true)
  -- leaves
  | .int _ | .flt _ | .str _ | .sym _ | .regexpLit .. | .tru | .fls | .nil | .self'
  | .var .. | .const _ | .vcall _ | .fwd | .retry' | .redo'
  | .cpath none _ | .splat none | .ret none | .brk none | .nxt none
  | .blockpass none => true

def declFreeAll : List Expr → Bool
  | [] => true
  | e :: es => declFree e && declFreeAll es

def declFreePairs : List (Expr × Expr) → Bool
  | [] => true
  | (k, v) :: ps => declFree k && declFree v && declFreePairs ps

def declFreeKw : List KwEntry → Bool
  | [] => true
  | .pair _ v :: es => declFree v && declFreeKw es
  | .dyn k v :: es => declFree k && declFree v && declFreeKw es
  | .splat e :: es => declFree e && declFreeKw es

def declFreeRescues :
    List (List Expr × Option (TargetKind × String) × Expr) → Bool
  | [] => true
  | (cls, _, handler) :: rs => declFreeAll cls && declFree handler && declFreeRescues rs

end

/-! ### `next` may not escape past an assignment — §F23

**A reachable soundness bug, found by reading `Judge.while'`'s semantic obligation** and
confirmed against CRuby (`corpus/…-while-next-escapes-unsafe`, `…-iter-block-next-escapes-unsafe`;
`found-issues.md` §F23). Both `Judge.while'` and `Judge.iterBlock` constrain the body's
**outgoing** environment — `Γb = Γ` for the loop, `capIntact … Γb'` for the block — and a `next`
leaves the iteration **mid-body**, at an environment neither premise mentions. So

```ruby
i = 0; x = 1
while i < 2
  i = i + 1; x = "s"
  next if i == 2
  x = 2
end
x + 1                     # x is "s": TypeError, and `validate` said Integer
```

was certified. The premise was being checked at the wrong point.

The fix is the conservative one the shape allows: **a `next` may only occur before anything has
assigned**, and then the environment at the escape *is* the body's incoming one, which is exactly
what the outgoing premise already pins. It keeps every climbed rung (`ctl-next`'s `next if x == 2`
is the body's first statement) and rejects both witnesses.

Recorded limitation, and it is `found-issues.md` §F13's: `noLocalAsgn` is **syntactic**, so a
`next` after a call to a closure that assigns a captured local is still accepted. That hole is
the fifteenth stall point's and is not made worse here. -/

mutual

/-- Does this expression contain no `next` that would escape to *this* body? A nested block,
loop or definition is a boundary: a `next` inside one belongs to it, not to us. -/
def nxtFree : Expr → Bool
  -- the escape itself
  | .nxt _ => false
  -- boundaries: an inner `next` belongs to the inner construct
  | .block .. | .def' .. | .defs .. | .class' .. | .module' .. => true
  | .scopedClass .. | .scopedModule .. | .sclass .. => true
  | .for' .. | .dowhile .. => true
  | .while' c _ => nxtFree c
  -- containers
  | .vasgn _ _ e | .splat (some e) | .ret (some e) | .brk (some e)
  | .blockpass (some e) | .cpath (some e) _ | .defined e | .casgn _ e
  | .cpathAsgn _ _ e => nxtFree e
  | .send recv _ args blk =>
    (match recv with | some r => nxtFree r | none => true) &&
    nxtFreeAll args &&
    (match blk with | some b => nxtFree b | none => true)
  | .seq es | .array es | .yield' es => nxtFreeAll es
  | .hash ps => nxtFreePairs ps
  | .kwargs entries => nxtFreeKw entries
  | .if' c t e =>
    nxtFree c && nxtFree t && (match e with | some x => nxtFree x | none => true)
  | .begin' body rescues els ens =>
    nxtFree body && nxtFreeRescues rescues &&
    (match els with | some x => nxtFree x | none => true) &&
    (match ens with | some x => nxtFree x | none => true)
  | .super' args blk =>
    nxtFreeAll args && (match blk with | some b => nxtFree b | none => true)
  | .zsuper blk => (match blk with | some b => nxtFree b | none => true)
  -- leaves
  | .int _ | .flt _ | .str _ | .sym _ | .regexpLit .. | .tru | .fls | .nil | .self'
  | .var .. | .const _ | .vcall _ | .fwd | .retry' | .redo'
  | .cpath none _ | .splat none | .ret none | .brk none
  | .undef .. | .alias' .. | .blockpass none => true

def nxtFreeAll : List Expr → Bool
  | [] => true
  | e :: es => nxtFree e && nxtFreeAll es

def nxtFreePairs : List (Expr × Expr) → Bool
  | [] => true
  | (k, v) :: ps => nxtFree k && nxtFree v && nxtFreePairs ps

def nxtFreeKw : List KwEntry → Bool
  | [] => true
  | .pair _ v :: es => nxtFree v && nxtFreeKw es
  | .dyn k v :: es => nxtFree k && nxtFree v && nxtFreeKw es
  | .splat e :: es => nxtFree e && nxtFreeKw es

def nxtFreeRescues :
    List (List Expr × Option (TargetKind × String) × Expr) → Bool
  | [] => true
  | (cls, _, handler) :: rs => nxtFreeAll cls && nxtFree handler && nxtFreeRescues rs

end

mutual

/-- Does this expression **assign no local**? Unlike `noLocalAsgn` — which is a whitelist of
shapes a *narrowing condition* may take, and answers `false` for anything it does not
recognise, `next` included — this is the honest question: is there a `vasgn` (or a `for`
target, or a block body that writes a captured local) anywhere in here.

Needed because §F23's premise is "no `next` **after an assignment**", and asking
`noLocalAsgn` instead rejects `next if c` itself — which is exactly the shape the climbed
`ctl-next` rung is built out of. Measured: the first version of this premise broke that rung. -/
def asgnFree : Expr → Bool
  -- the assignments
  | .vasgn .. => false
  | .for' .. => false
  -- a block can write a local it captured
  | .block _ _ body => asgnFree body
  -- containers
  | .splat (some e) | .ret (some e) | .brk (some e) | .nxt (some e)
  | .blockpass (some e) | .cpath (some e) _ | .defined e | .casgn _ e
  | .cpathAsgn _ _ e => asgnFree e
  | .send recv _ args blk =>
    (match recv with | some r => asgnFree r | none => true) &&
    asgnFreeAll args &&
    (match blk with | some b => asgnFree b | none => true)
  | .seq es | .array es | .yield' es => asgnFreeAll es
  | .hash ps => asgnFreePairs ps
  | .kwargs entries => asgnFreeKw entries
  | .if' c t e =>
    asgnFree c && asgnFree t && (match e with | some x => asgnFree x | none => true)
  | .while' c body => asgnFree c && asgnFree body
  | .dowhile body cond => asgnFree body && asgnFree cond
  | .begin' body rescues els ens =>
    asgnFree body && asgnFreeRescues rescues &&
    (match els with | some x => asgnFree x | none => true) &&
    (match ens with | some x => asgnFree x | none => true)
  | .super' args blk =>
    asgnFreeAll args && (match blk with | some b => asgnFree b | none => true)
  | .zsuper blk => (match blk with | some b => asgnFree b | none => true)
  -- declarations bind no local of *this* frame
  | .def' .. | .defs .. | .class' .. | .module' .. => true
  | .scopedClass .. | .scopedModule .. | .sclass .. => true
  | .undef .. | .alias' .. => true
  -- leaves
  | .int _ | .flt _ | .str _ | .sym _ | .regexpLit .. | .tru | .fls | .nil | .self'
  | .var .. | .const _ | .vcall _ | .fwd | .retry' | .redo'
  | .cpath none _ | .splat none | .ret none | .brk none | .nxt none
  | .blockpass none => true

def asgnFreeAll : List Expr → Bool
  | [] => true
  | e :: es => asgnFree e && asgnFreeAll es

def asgnFreePairs : List (Expr × Expr) → Bool
  | [] => true
  | (k, v) :: ps => asgnFree k && asgnFree v && asgnFreePairs ps

def asgnFreeKw : List KwEntry → Bool
  | [] => true
  | .pair _ v :: es => asgnFree v && asgnFreeKw es
  | .dyn k v :: es => asgnFree k && asgnFree v && asgnFreeKw es
  | .splat e :: es => asgnFree e && asgnFreeKw es

def asgnFreeRescues :
    List (List Expr × Option (TargetKind × String) × Expr) → Bool
  | [] => true
  | (cls, _, handler) :: rs => asgnFreeAll cls && asgnFree handler && asgnFreeRescues rs

end

/-- The statement walk: a `next` is allowed while nothing has assigned, and not after. -/
def nxtPrefixGo : List Expr → Bool
  | [] => true
  | s :: rest => if asgnFree s then nxtPrefixGo rest else nxtFree s && nxtFreeAll rest

/-- **§F23's premise**: in this body, no `next` follows an assignment — so every `next` escapes
at the body's *incoming* environment, which the enclosing rule's outgoing premise already pins. -/
def nxtPrefixOk : Expr → Bool
  | .seq es => nxtPrefixGo es
  | e => asgnFree e || nxtFree e

/-- Is a method of this name **declared** at all — the raw table lookup, with no
callability filter. Read by `Judge.bareName`, whose premise means "this name is not a method
of the program" and must not be weakened by `defGet?`'s guard: a `def x` whose body declares
is still a `def x`, and a `vcall x` that reaches it is not a `NameError`. -/
def defDeclared? (D : DefTable) (m : String) : Option Defn := D.find? (·.name == m)

/-- The method a call rule may type against: declared, **and** with a body that declares
nothing (§F3 above). Every body-fetching lookup in this file goes through here — top-level
methods, instance and singleton methods (`defGet? c.methods`, `mroGet?`), and `resolveAliases`
— so the guard is stated once. -/
def defGet? (D : DefTable) (m : String) : Option Defn :=
  match D.find? (·.name == m) with
  | some d => if declFree d.body then some d else none
  | none => none

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

/-! ### A class body's constants (tier 13)

`Ctx.consts` maps a constant's absolute path to its type, and it is grown by `extendConsts`,
which is a **function of syntax alone** — `Ctx.afterStmt` gets the statement's type, and that
is the type of the `class` statement (`.any`), not of anything inside its body.

So a class-body constant's type has to be readable off its initializer's syntax. That is
`constLitTy?`, and its restriction to literals is the price of this tier's second rung. The
restriction is not the soundness argument, though — `constLitTy?` is just a guess until
`Judge.classStmt`'s `JudgeConsts` premise **judges the initializer at exactly that type**, in
the context in force at the class statement. Two things follow:

- soundness of `constLitTy?` reduces to soundness of `Judge`, so this function may be widened
  freely: a wrong row costs a rung (the premise fails) and never a wrong type;
- and the judgment happens at the **definition site**. That matters more than it looks.
  Judging the initializer lazily, at each *read*, is unsound: `κ.classes` only grows, a
  reopened class can redefine a method, and `class Box; V = Helper.new.f; end` re-judged after
  `class Helper; def f; "s"; end; end` would type `V` as a `String` while it holds the
  `Integer` the original `f` returned.

Top-level constants need none of this: their type comes from the judgment directly, because
there `Ctx.afterStmt` is handed the statement's own type. -/
mutual

def constLitTy? : Expr → Option Ty
  | .int _ => some .int
  | .flt _ => some .float
  | .str _ => some (.cls "String")
  | .sym _ => some .sym
  | .tru => some .bool
  | .fls => some .bool
  | .nil => some .nilT
  -- A hash literal's type carries nothing about its pairs (tier 5), so this row could read
  -- `.hash _ => some (.cls "Hash")` and be right about the type. It checks the pairs anyway,
  -- because `constLitTy?_sound` — "an expression this function types really does have that
  -- type, in any context, unconditionally" — is what lets the same function be used for an
  -- **optional parameter's default** (tier 14a) with no premise anywhere to discharge, and
  -- that theorem needs the pairs to type.
  | .hash pairs =>
    match constLitPairTys? pairs with
    | some (kτ, vτ) => some (.hashOf kτ vτ)
    | none => none
  | .array es => (constLitTys? es).map (fun τs => .arrayOf (elemTy τs))
  -- `.freeze` is the idiom every frozen constant table in the slice is written with, and it is
  -- the identity on the value (`PrimSig.freezeId`), so it is the identity here.
  | .send (some r) "freeze" [] none => constLitTy? r
  | _ => none

def constLitTys? : List Expr → Option (List Ty)
  | [] => some []
  | e :: es => match constLitTy? e, constLitTys? es with
    | some τ, some τs => some (τ :: τs)
    | _, _ => none

/-- The joined key and value types of a **literal** hash, folded exactly as `JudgePairs`
folds them (tier 17b). Replaced `constLitPairs?`, which only asked whether the pairs typed --
now the types are the answer. -/
def constLitPairTys? : List (Expr × Expr) → Option (Ty × Ty)
  | [] => some (.never, .never)
  | (k, v) :: ps =>
    match constLitTy? k, constLitTy? v, constLitPairTys? ps with
    | some kτ, some vτ, some (kr, vr) => some (joinT kτ kr, joinT vτ vr)
    | _, _, _ => none

end

/-! ### The environment a method body starts in

**Only its parameters**, bound to what the call site supplied. Two decisions in one small
function:

- **A fresh environment, not the caller's.** A Ruby method body does not see the caller's
  locals, so the body is judged in `paramBind`'s result and the call's *outgoing* environment
  is the caller's own (after the arguments), never the body's.
- **Matching is greedy, left to right**, and the reason that is safe is worth stating: it
  either agrees with Ruby or fails. Ruby fills post-optional and post-rest *required*
  parameters first (`def f(a, b = 1, c)` with two arguments binds `a` and `c`), and greedy
  matching there binds `a` and `b`, then meets a `.req` with no argument left, and answers
  `none`. There is no argument count at which greedy succeeds with a binding Ruby would not
  have made. Length mismatch is also `none`, which is what rejects `fun-wrong-arity`.

### One walk, three entry points (tier 14c)

`paramEnv`, `paramEnvB` and the keyword-aware binder are the *same* left-to-right walk over a
parameter list, differing only in what is available to bind from. So there is one function,
`paramBind`, taking all three inputs — the block (out of band), the positional argument types,
and the keyword arguments as name/type pairs — and the two older names are abbreviations for it
at empty inputs. Every derivation on file still discharges its `paramEnv … = some Γb` premise by
`rfl`, because `paramBind`'s behaviour at `kws = []` on required parameters is unchanged.

One behaviour did change on the way, in the direction of being more right: `paramEnv` used to
refuse a `Param.block` outright (only `paramEnvB` accepted one), and now binds it to `.nilT`,
which is what Ruby does when a method with a `&b` parameter is called with no block. -/
def kwGet? (kws : List (String × Ty)) (k : String) : Option Ty :=
  (kws.find? (·.1 == k)).map (·.2)

/-- Drop the *matched* keyword, so that whatever is left at the end of the walk is the set of
keywords the method has no parameter for — which raises `ArgumentError`, inside the family. -/
def kwErase : List (String × Ty) → String → List (String × Ty)
  | [], _ => []
  | (k, τ) :: kws, x => if k == x then kwErase kws x else (k, τ) :: kwErase kws x

/-- **Is every remaining parameter one that cannot consume a positional argument?** The exact
condition under which a rest parameter may be greedy: `def f(*a, b)` fails it (Ruby binds
`b` first), while `def f(*a, c:, **kw, &blk)` passes, because keywords, a keyword-rest and a
block all come from somewhere other than the positional list.

Tier 14b stated this as "the rest parameter must be last", which was the same condition for the
parameter kinds that existed then. -/
def noPositionalParams (ps : List Param) : Bool :=
  ps.all (fun p => match p with
    | .key _ _ | .kwrest _ | .block _ => true
    | _ => false)

def paramBind (blk : Option Ty) : List Param → List Ty → List (String × Ty) → Option Env
  -- Every parameter bound and every argument consumed. **The `kws.isEmpty` check is a
  -- soundness condition**, not tidiness: a keyword the method has no parameter for raises
  -- `ArgumentError` (tier 14c).
  | [], [], kws => if kws.isEmpty then some [] else none
  | .req x :: ps, τ :: τs, kws => (paramBind blk ps τs kws).map (fun Γ => (x, τ) :: Γ)
  -- Tier 14a: an **optional** parameter. Two cases, and the matching is greedy left to right.
  -- An argument was supplied, so the default is irrelevant:
  | .opt x _ :: ps, τ :: τs, kws => (paramBind blk ps τs kws).map (fun Γ => (x, τ) :: Γ)
  -- Or it was not, and the parameter holds the default's value. Its type comes from
  -- `constLitTy?`, which needs no premise to license it: `constLitTy?_sound` says an
  -- expression this function types really has that type in *any* context, unconditionally.
  -- A non-literal default (`def pad(s, n = s.length)`) is `none` here — see §Frontier.
  | .opt x d :: ps, [], kws =>
    match constLitTy? d with
    | some τ => (paramBind blk ps [] kws).map (fun Γ => (x, τ) :: Γ)
    | none => none
  -- Tier 14b: a **rest** parameter. The element type is `elemTy` of the argument types it
  -- swallows, exactly as for an array literal, which makes the zero-argument case
  -- `arrayOf .never`: the array really is empty, and `.never` is the most precise thing to say
  -- about the elements of an empty array (see `elemTy`, and `IterSig.injectEmpty` for what
  -- consumes it). Greedy only when `noPositionalParams` holds.
  | .rest (some x) :: ps, τs, kws =>
    if noPositionalParams ps then
      (paramBind blk ps [] kws).map (fun Γ => (x, .arrayOf (elemTy τs)) :: Γ)
    else none
  | .rest none :: ps, _, kws =>
    if noPositionalParams ps then paramBind blk ps [] kws else none
  -- Tier 14c: a **keyword** parameter, matched **by name** and only once the positional list is
  -- exhausted, because a keyword parameter never consumes a positional argument. Three
  -- outcomes, and the third is the soundness one: supplied, defaulted, or **missing and
  -- required**, which raises `ArgumentError`.
  | .key k dflt :: ps, [], kws =>
    match kwGet? kws k with
    | some τ => (paramBind blk ps [] (kwErase kws k)).map (fun Γ => (k, τ) :: Γ)
    | none =>
      match dflt with
      | some d =>
        match constLitTy? d with
        | some τ => (paramBind blk ps [] kws).map (fun Γ => (k, τ) :: Γ)
        | none => none
      | none => none
  -- A keyword-rest collects everything left, and tier 17b gives it a *useful* type: the keys
  -- are symbols (the call site wrote `k: v`) and the value type is the join of what was
  -- passed, folded exactly as a hash literal's is.
  | .kwrest (some x) :: ps, [], kws =>
    (paramBind blk ps [] []).map
      (fun Γ => (x, .hashOf .sym (elemTy (kws.map (·.2)))) :: Γ)
  | .kwrest none :: ps, [], _ => paramBind blk ps [] []
  | .block (some x) :: ps, τs, kws =>
    (paramBind blk ps τs kws).map (fun Γ => (x, blk.getD .nilT) :: Γ)
  | .block none :: ps, τs, kws => paramBind blk ps τs kws
  | _, _, _ => none

def paramEnv (ps : List Param) (τs : List Ty) : Option Env := paramBind none ps τs []

/-- **Split a call's argument list into positional arguments and a trailing `kwargs`**
(tier 14c). `Expr.kwargs` only ever occurs as the last element of an argument list (see its
docstring), and it is *not a value* — so it cannot be typed by `JudgeAll` and every call shape
that admits keywords needs the split.

`none` when there is no trailing `kwargs`, which is the ordinary call and the arm already on
file. `splitKw?_sound` (`Proof/ChkSound.lean`) is the bridge to the rule, which states the
split as `args = pos ++ [.kwargs entries]` rather than as a call to this function. -/
def splitKw? : List Expr → Option (List Expr × List KwEntry)
  | [.kwargs es] => some ([], es)
  | e :: rest => (splitKw? rest).map (fun p => (e :: p.1, p.2))
  | [] => none

/-- The name a keyword-carrying call binds its parameters through; `paramEnv` is this at no
keywords, and the two are deliberately the same function so that a rule written for one shape
cannot disagree with the other about arity. -/
def paramEnvK (ps : List Param) (τs : List Ty) (kws : List (String × Ty)) : Option Env :=
  paramBind none ps τs kws

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
  /-- `SIZE = 3` in a class body (tier 13) — a **constant**, carried as its unjudged
      initializer, because the class table is built by a syntactic function and a type is not
      syntactic. What closes that gap is `constLitTy?` plus `JudgeConsts`: see
      `Judge.classStmt`. -/
  | constM (n : String) (e : Expr)
  /-- `attr_reader :x, :y` (tier 13d) — *n* method declarations in one statement.
      `splitMembers` expands each name into the `def x; @x; end` it stands for, so nothing
      downstream knows this member kind existed. -/
  | attrR (names : List String)
  /-- `alias length size` (tier 13d). Resolved by `classMethods?`, not here: an alias copies a
      method that has to be found first, and only the whole member list knows what is
      there. -/
  | aliasM (newName oldName : String)
  /-- `private_constant :SECRET` (tier 13d). Declares nothing, so `splitMembers` drops it;
      what reads it is `privNames`, from `Ctx.afterStmt`. -/
  | privC (names : List String)
  /-- A **nested class or module** (tier 13e): `module M; class Box; … end; end`. The flag is
      `Cls.isModule`'s. Carried as its unread body, because everything about it — its own
      members, its own constants, its own nested declarations — has to be recomputed under
      the *qualified* name `M::Box`, and only the enclosing statement knows the prefix. -/
  | nestedM (isMod : Bool) (name : String) (body : Expr)

/-- A list of send arguments as bare symbol names, or `none` if any argument is anything
else. `attr_reader`/`private_constant` are declarations, so an argument this cannot read has
to make the whole member unreadable rather than be skipped. -/
def symNames? : List Expr → Option (List String)
  | [] => some []
  | .sym n :: es => (symNames? es).map (fun ns => n :: ns)
  | _ => none

/-- The methods `attr_reader :x` stands for: `def x; @x; end`, one per name. The ivar's name
is the reader's with an `@`, which is Ruby's rule and the only thing there is to know about
`attr_reader`. -/
def attrDefns : List String → List Defn
  | [] => []
  | n :: ns => ⟨n, [], .var .ivar ("@" ++ n)⟩ :: attrDefns ns

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
  -- Tier 13: a constant. Unlike a `def`, a `casgn` in a class body **executes** when the
  -- class statement runs, which is why it is the first member kind `classStmt` has to type
  -- rather than merely record.
  | .casgn n e => some (.constM n e)
  -- Tier 13d. All three are the same kind of thing as `include`: an ordinary class-body
  -- statement that this checker reads *declaratively*, matched at the exact syntax the
  -- desugarer emits. The arguments must be bare symbol literals; `attr_reader(*names)` is not
  -- read, so the class does not enter the table and nothing using it types.
  | .send none "attr_reader" args none => (symNames? args).map ClsMember.attrR
  | .send none "private_constant" args none => (symNames? args).map ClsMember.privC
  | .alias' newName oldName => some (.aliasM newName oldName)
  -- Tier 13e. A nested class with a **superclass** is deliberately not read: the superclass
  -- name would need resolving against the nesting too, and refusing the member here makes the
  -- *enclosing* class unreadable rather than silently dropping the nested one.
  | .class' n none body => some (.nestedM false n body)
  | .module' n body => some (.nestedM true n body)
  | _ => none

abbrev Nested := List (Bool × String × Expr)

def splitMembers :
    List ClsMember →
      List Defn × List Defn × List String × List String × List String ×
        List (String × Expr) × List (String × String) × Nested
  | [] => ([], [], [], [], [], [], [], [])
  | .inst d :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (d :: i, s, c, e, p, k, a, z)
  | .sing d :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, d :: s, c, e, p, k, a, z)
  | .incl n :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, s, n :: c, e, p, k, a, z)
  | .ext n :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, s, c, n :: e, p, k, a, z)
  | .prep n :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, s, c, e, n :: p, k, a, z)
  | .constM n e :: ms =>
    let (i, s, c, e', p, k, a, z) := splitMembers ms; (i, s, c, e', p, (n, e) :: k, a, z)
  -- Tier 13d: expanded here, so no later function knows `attr_reader` exists.
  | .attrR ns :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (attrDefns ns ++ i, s, c, e, p, k, a, z)
  | .aliasM nw od :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, s, c, e, p, k, (nw, od) :: a, z)
  -- `private_constant` declares nothing; it is read off the body separately (`privNames`).
  | .privC _ :: ms => splitMembers ms
  | .nestedM im n b :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, s, c, e, p, k, a, (im, n, b) :: z)

/-- `alias new old` copies the method `old` names, so it can only be resolved once the whole
member list is known — which is why it is `classMethods?`'s job and not `clsMember?`'s.

**An unresolvable alias makes the whole class unreadable** (`none`), rather than being
skipped. Ruby raises `NameError` for `alias b a` with no `a`, and `NameError` is outside this
package's type-stuck family, so skipping would have been "sound" and useless: the class would
enter the table missing a method, and a later dispatch would fail for the wrong reason.

What this does *not* enforce is Ruby's ordering requirement — the aliased method must be
defined *before* the `alias` line. `splitMembers` keeps each kind's source order but loses the
interleaving between kinds, so `class C; alias b a; def a; 1; end; end` is accepted here and
raises `NameError` in Ruby. Outside the family, and recorded rather than fixed. -/
def resolveAliases : List Defn → List (String × String) → Option (List Defn)
  | ms, [] => some ms
  | ms, (nw, od) :: as =>
    match defGet? ms od with
    | some d => resolveAliases (⟨nw, d.params, d.body⟩ :: ms) as
    | none => none

def finishMembers :
    List Defn × List Defn × List String × List String × List String ×
      List (String × Expr) × List (String × String) × Nested →
    Option (List Defn × List Defn × List String × List String × List String ×
      List (String × Expr) × Nested)
  | (ms, sms, incs, exts, preps, cs, als, nst) =>
    (resolveAliases ms als).map (fun ms' => (ms', sms, incs, exts, preps, cs, nst))

/-- A class body's instance and singleton methods, or `none` if the body contains anything
this checker cannot read.

**That `none` is doing two jobs at once**, which is why the restriction sits in one place.
It is what makes the body safe to *evaluate* unchecked — a `def`/`defs` statement never runs
its body, and `nil` is `nil`, so a body made only of those cannot be type-stuck — and it is
what makes the class readable into `CTable`. A body with an ivar assignment at class level, a
nested class, or anything executable is not typed at all: conservative in the direction that
costs rungs rather than soundness, and it is the shape every tier-7 rung has.

**Tier 13 punched the one hole in "nothing executable".** A `casgn` in a class body *does*
run when the class statement runs, so admitting it means `classStmt` has to type it rather
than merely record it — which is exactly what its `JudgeConsts` premise does. The sixth
component of the tuple is those constants, paired with their unjudged initializers. -/
def classMethods? :
    Expr → Option (List Defn × List Defn × List String × List String × List String ×
      List (String × Expr) × Nested)
  | .nil => some ([], [], [], [], [], [], [])
  | .seq es => (es.mapM clsMember?).bind (fun ms => finishMembers (splitMembers ms))
  | e => (clsMember? e).bind (fun m => finishMembers (splitMembers [m]))

/-- The absolute path of a constant defined at top level. -/
def constKey (n : String) : String := "::" ++ n

/-- The absolute path of a constant defined in the body of class-or-module `owner`. -/
def constKeyIn (owner n : String) : String := "::" ++ owner ++ "::" ++ n

/-- Every constant a **class or module statement** binds, as path/type pairs. Skips any
initializer `constLitTy?` cannot read — which costs nothing, because `Judge.classStmt` would
not have typed the statement at all in that case. -/
def addClassConsts (S : Env) (owner : String) : List (String × Expr) → Env
  | [] => S
  | (n, e) :: cs =>
    addClassConsts (match constLitTy? e with
                    | some τ => envSet S (constKeyIn owner n) τ
                    | none => S) owner cs

/-- The same, for the constants of **nested** declarations (tier 13e), whose owner is the
qualified name. Fuel-bounded for `nestedClasses`' reason and with the same consequence: a
dropped constant is a rejected read. -/
def addNestedConsts (S : Env) : Nat → String → Nested → Env
  | 0, _, _ => S
  | _ + 1, _, [] => S
  | k + 1, pfx, (_, n, body) :: rest =>
    let q := pfx ++ "::" ++ n
    let S' := match classMethods? body with
      | some (_, _, _, _, _, cs, nst) => addNestedConsts (addClassConsts S q cs) k q nst
      | none => S
    addNestedConsts S' k pfx rest

/-- The constant members of a class body, or `[]` if the body is not one this checker reads.
Deliberately re-derived from `classMethods?` rather than passed in: `extendConsts` is called
from `Ctx.afterStmt`, which sees only the statement. -/
def bodyConsts (body : Expr) : List (String × Expr) :=
  match classMethods? body with
  | some (_, _, _, _, _, cs, _) => cs
  | none => []

/-! ### `private_constant` (tier 13d)

`private_constant :SECRET` does not change what the constant *is*; it changes who may name
it. `Box::SECRET` from outside raises `NameError`, while a bare `SECRET` inside a method of
`Box` still reads it. So the fact belongs on the *scoped read* rule and nowhere else, and it
is **precision rather than soundness** — `NameError` is outside this package's type-stuck
family, so a checker that ignored `private_constant` would still be sound and would certify
`Box::SECRET`, a program Ruby refuses to run. That is the whole reason this field exists.

It is a second syntactic pass over the class body rather than a component of
`classMethods?`'s tuple, because `splitMembers` drops the member (it declares nothing) and
`Ctx.afterStmt` is where the answer is needed. -/
mutual

def privNames : Expr → List String
  | .send none "private_constant" args none => (symNames? args).getD []
  | .seq es => privNamesAll es
  | _ => []

def privNamesAll : List Expr → List String
  | [] => []
  | e :: es => privNames e ++ privNamesAll es

end

/-- The absolute keys a class-or-module statement makes private. -/
def addPrivNames (P : List String) (owner : String) : List String → List String
  | [] => P
  | n :: ns => addPrivNames (constKeyIn owner n :: P) owner ns

def extendPrivConsts (P : List String) : Expr → List String
  | .class' n _ body => addPrivNames P n (privNames body)
  | .module' n body => addPrivNames P n (privNames body)
  | _ => P

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

/-! ### Is this name an exception class? (tier 16b)

A builtin exception name, or a declared class whose superclass chain reaches one. Fuel-bounded
for `nestedClasses`' reason — a `Cls.super?` walk has no structural measure — and running out
answers `false`, which is a rejected `raise` rather than a wrong one. -/
def excNameUp (C : CTable) : Nat → String → Bool
  | 0, _ => false
  | k + 1, n =>
    if excCls? n then true
    else
      match clsGet? C n with
      | some c => match c.super? with
                  | some sn => excNameUp C k sn
                  | none => false
      | none => false

def excName? (C : CTable) (n : String) : Bool := excNameUp C 32 n

/-- The class names a `rescue` clause lists, or `none` if any of them is not a bare constant.
`rescue foo()` is not read, so the whole `begin` is not typed. -/
def rescueClasses? : List Expr → Option (List String)
  | [] => some []
  | .const n :: es => (rescueClasses? es).map (fun ns => n :: ns)
  | _ => none

/-- The environment a `rescue … => e` binding contributes, prepended to the handler's.

**Only a single builtin exception class may be bound**, and that is a restriction rather than a
principle: `.cls n` for an `ExcCls` name is a type this judgment can say something about
(`PrimSig.excMessage`), whereas a user exception would want `.inst n .ivar0` and a rescue over
*several* classes would want their union. Neither is hard; no rung asks. A clause with no
binding is always fine. -/
def rescueBind? (names : List String) : Option (TargetKind × String) → Option Env
  | none => some []
  | some (.lvar, x) =>
    match names with
    | [n] => if excCls? n then some [(x, .cls n)] else none
    | _ => none
  | some _ => none

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
  -- **`.arrayOf`/`.hashOf` are deliberately absent**, and the reason is a denotation fact
  -- rather than a table gap: their `denM` arms read the *payload* (`arrElems?`/`hshEntries?`)
  -- and say nothing about the object's class, so a value of type `.arrayOf τ` need not be an
  -- `Array` as far as the denotation is concerned — and a **negative** `is_a?` answer about it
  -- would be a claim this judgment cannot make. Dropping the rows costs only precision, and
  -- only in one direction: the *positive* answer is what `isATy` keeps the type for, and
  -- `isAAnswer = none` keeps it too. (`Ty.arrayOf`'s docstring is where the class fact would
  -- have to be added if a rung ever wants the row back; see `found-issues.md` §F12 for the
  -- shape such a change takes.)
  | _ => none

/-- **Is every class in this chain free of mixins, as far as the context knows?**
`found-issues.md` §F9's guard. A chain is a list of *names*, and `isAAnswer` answers `is_a?`
negatively off it — so a name in it whose class the context reopens with an `include` or a
`prepend` has an ancestor the chain does not mention, and the negative answer is wrong. This
does not have to walk: it is the mixin lists of the chain's own members that matter, and
`mixinAncestors?` has already refused any chain whose *modules* are themselves impure. -/
def mixinFreeChain (C : CTable) (ch : List String) : Bool :=
  ch.all (fun n => match clsGet? C n with
    | none => true
    | some c => c.includes.isEmpty && c.prepends.isEmpty)

/-- **Does any declared class descend from `n`?** — and the answer `isAAnswer` needs is "no".

The second half of §F9's guard, and it is about a different direction of the same gap.
`mixinFreeChain` asks whether the classes *in* a chain gained ancestors; this asks whether a
class was declared *below* the chain's base. Both break the negative answer, and for `.cls`/
`.arrayOf`/`.hashOf` types it is this one that matters: those denote **is-a**
(`Denote/Den.lean`), so a value of type `.cls "String"` may be an instance of a declared
subclass, whose own name is in *its* ancestors and in no static chain.

Measured at the booted machine before the guard was written: no boot class descends from any of
`Integer`, `Float`, `NilClass`, `Symbol`, `String`, `Hash` or `Array`. So the *heap* side of
the claim needs only the context to be quiet, which is what this checks.

A chain that leaves the table counts as "might descend", for `ancestorsUp`'s reason. -/
def noDeclaredBelow (C : CTable) (n : String) : Bool :=
  C.all (fun c =>
    c.name == n ||
    (match ancestors? C c.name with
     | some ch => !(ch.contains n)
     | none => false))

/-- The two conditions a **negative** `is_a?` answer off a static chain needs: nothing was
mixed into the chain, and nothing was declared below its base. -/
def isANoOk (C : CTable) (ch : List String) : Bool :=
  mixinFreeChain C ch &&
  (match ch.head? with
   | some base => noDeclaredBelow C base
   | none => false)

/-- `is_a?(cn)` on a value of type `τ`: `some true` when **every** value of `τ` answers
`true`, `some false` when every value answers `false`, and `none` when this judgment cannot
tell — which is the answer for `.any`, `.bool`, a `.cls` outside `builtinAncestors`, and a
declared class whose chain leaves the table.

Not defined on `.union`/`.nilable`: those are not a single class, and treating them here
would hide the fact that a union's answer is per-member. `isATy`/`notATy` decompose them. -/
def isAAnswer (C W : CTable) (cn : String) : Ty → Option Bool
  | .inst n _ => (ancestors? C n).bind (fun ch =>
      if (ch ++ rootAncestors).contains cn then some true
      -- `ancestors?` checked the *declared* chain's mixins; `rootAncestors` is appended
      -- blindly, so `class Object; include M; end` is the case this guard covers
      else if mixinFreeChain W rootAncestors then some false else none)
  -- **§F9**: the builtin chain is a *static table*, and `class Integer; include M; end` really
  -- does make `5.is_a?(M)` true; and the type denotes **is-a**, so a declared subclass's
  -- instance is one of its values. So *neither* answer is available at a context that has
  -- disturbed the chain.
  --
  -- The positive answer would survive on its own (a mixin only adds ancestors, and a subclass
  -- keeps them) and an earlier version of this guard kept it. It is gated anyway, because
  -- proving the positive half without `isANoOk`'s no-subclasses clause needs **transitivity of
  -- the ancestor walk** — a general fact about `ancestors` that nothing on file proves, and one
  -- that a `StateOk` component has no business assuming. Gating costs precision only where a
  -- program mixes into or subclasses a core class, and buys the exactness the proof uses.
  | τ => (builtinAncestors τ).bind (fun ch =>
      if isANoOk W ch then (if ch.contains cn then some true else some false) else none)

/-- **Does any *declared* class descend from `n` and redefine `m`?** — `found-issues.md`
§F11's guard, and the answer it wants is "no".

`Ty.cls n`'s denotation is `is_a?`, deliberately: `rescue StandardError => e` binds whatever
was raised, and that is normally an instance of a **subclass**. So a `PrimSig` row at a
nominal receiver — `Exception#message` is the one the target uses — is a claim about a method
the receiver's *actual* class resolves, and a declared subclass that redefines the name
resolves it differently. `PrimSig` cannot see the class table (that is what makes it a table
rather than a judgment), so the check lives here and is a premise of `Judge.prim`.

Precise rather than structural, in the same way `isADispatchOk` is: it asks whether a class
that really descends from `n` really declares `m`, not whether the program mentions the name
anywhere. `ancestors?` answering `none` — a chain that leaves the table — counts as "might
descend", because a class whose superclass is unknown might be under `n`.

**`valueClsNames` is exempt, and the exemption is an argument, not a shortcut.** A value gets a
nominal type *strictly larger than its class* in exactly one place in this judgment:
`rescueBind?`, because `rescue C => e` binds whatever was raised and Ruby lets that be a
subclass. Every other `.cls n` — the four names below, which are all `PrimSig` mentions — is
produced by a literal or by a builtin and is therefore an instance of exactly `n` (the same
exactness-by-construction argument §F8 records, and subject to the same caveat). Exempting them
is what keeps `constLitTy?_sound` unconditional: that theorem types `"s".freeze` in **any**
context, so a premise it cannot discharge would have to be pushed onto every one of its
callers, none of which has a class table to check. -/
def valueClsNames : List String := ["String", "Hash", "Regexp", "MatchData"]

def primDispatchOk (C : CTable) (σ : Ty) (m : String) : Bool :=
  match σ with
  | .cls n =>
    if valueClsNames.contains n then true
    else
      C.all (fun c =>
        (c.methods.find? (·.name == m)).isNone ||
        (match ancestors? C c.name with
         | some ch => !(ch.contains n)
         | none => false))
  | _ => true

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

/-! ### Nested namespaces (tier 13e)

`module M; class Box; … end; end` gives a class whose name **is** `"M::Box"` — that is what
CRuby's `Box.name` answers, and matching it means the `CTable` key, `Ty.clsOf` and `Ty.inst`
all agree with the runtime rather than with a convention this package invented.

The recursion is **fuel-bounded**, and unlike `chk`'s fuel this one bounds *breadth as well as
depth*: `nestedClasses` spends a unit per nested declaration visited in either direction. The
reason is termination — the nested bodies come out of `classMethods?`, which Lean cannot see
as returning subterms of its argument, so there is no structural measure to recurse on. It is a
completeness knob like every other fuel here: running out drops a table entry, and a dropped
entry means a later use of that class finds nothing and is rejected.

`nestFuel` is generous for a source file (the deepest nesting in the target is three, with
tens of siblings) and finite, which is all the kernel needs. -/
def nestFuel : Nat := 512

/-- Every class-or-module entry a nested declaration list contributes, with names qualified by
`pfx`. Flat, so the caller folds `mergeCls` over it — which is what makes a *reopened* nested
class merge with its earlier definition exactly as a top-level one does. -/
def nestedClasses : Nat → String → Nested → List Cls
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | k + 1, pfx, (isMod, n, body) :: rest =>
    let q := pfx ++ "::" ++ n
    (match classMethods? body with
     | some (ms, sms, incs, exts, preps, _, nst) =>
       { name := q, super? := none, methods := ms, smethods := sms, isModule := isMod,
         includes := incs, prepends := preps, extended := exts }
         :: nestedClasses k q nst
     | none => []) ++ nestedClasses k pfx rest

def mergeAll (C : CTable) : List Cls → CTable
  | [] => C
  | c :: cs => mergeAll (mergeCls C c) cs

/-- The nested declarations of a class body, or `[]` if the body is not one this checker
reads — `bodyConsts`'s twin, and re-derived from `classMethods?` for the same reason. -/
def bodyNested (body : Expr) : Nested :=
  match classMethods? body with
  | some (_, _, _, _, _, _, nst) => nst
  | none => []

def extendClasses (C : CTable) : Expr → CTable
  | .class' n sup body =>
    match classMethods? body with
    | some (ms, sms, incs, exts, preps, _, _) =>
      -- Tier 13e: `mergeAll … (nestedClasses …)` is the only addition, and it is the same in
      -- both arms and in `module'` below: whatever this statement declares, its nested
      -- declarations are declared with it, under its name as prefix.
      match sup with
      | none =>
        mergeAll (mergeCls C
          { name := n, super? := none, methods := ms, smethods := sms, isModule := false
            includes := incs, prepends := preps, extended := exts })
          (nestedClasses nestFuel n (bodyNested body))
      | some (.const sn) =>
        mergeAll (mergeCls C
          { name := n, super? := some sn, methods := ms, smethods := sms, isModule := false
            includes := incs, prepends := preps, extended := exts })
          (nestedClasses nestFuel n (bodyNested body))
      -- A superclass expression that is not a bare constant (`class C < foo()`) is not
      -- read, so the class does not enter the table and nothing using it is typed.
      | some _ => C
    | none => C
  -- Tier 8. A module is a `Cls` with no superclass and the module flag set; the body is read
  -- by the same `classMethods?`, so `def self.foo` lands in `smethods` and `M.foo` is
  -- `callSMethod` with nothing added.
  | .module' n body =>
    match classMethods? body with
    | some (ms, sms, incs, exts, preps, _, _) =>
      mergeAll (mergeCls C
        { name := n, super? := none, methods := ms, smethods := sms, isModule := true
          includes := incs, prepends := preps, extended := exts })
        (nestedClasses nestFuel n (bodyNested body))
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

/-- The closure a call rule may type against. Same guard as `defGet?` and for the same reason
(`found-issues.md` §F3): `closCall`, `iterClosPass` and `yieldExpr` all type `c.body` and then
conclude at the caller's `κ`, so a block body containing a `def` would carry a stale table out
of the call. A block whose body declares still gets a `Ty.clos` from `lambdaLit` — the type says
nothing about the tables — it just cannot be *called* by this checker. -/
def closGet? (K : ClosTable) (k : Nat) : Option Clos :=
  match K[k]? with
  | some c => if declFree c.body then some c else none
  | none => none

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

/-! ## The context, split by polarity (`context-splitting.md`)

`Ctx` used to be one flat record of nine fields, and `context-splitting.md` §1 measured why
that was wrong: the fields have **three different disciplines** and the single record threaded
none of them. They are now three structures.

* **`Pos`** — facts that only ever *grow* along program order. Every premise that reads one is
  a **lookup** ("the table contains at least this fact"), so `PosOk` is a `∀`-over-a-set and
  weakening to a subset is one line.
* **`Neg`** — facts that only ever *shrink*. Every premise that reads one is a **membership**,
  not a miss in `Pos`: absence is its own fact, seeded whole-program (§2.2), not the complement
  of whatever `extendDefs` happened to reconstruct. That is `found-issues.md` §F20's fix.
* **`Scope`** — lexical, rebound on entry to a body, and never reported out. `Ctx.inMethod`
  already drew this line; this names it.

Only `Pos` and `Neg` thread (`Judge`'s `κ'`); `Scope` is pinned equal by every rule. -/

/-- A **receiver port**: the two method-lookup relations this checker walks
(`context-splitting.md` §4.6). `inst C` is `mroList?`/`mroGet?`'s chain — prepends, `C`,
includes, then the superclass chain. `cls C` is `lookupUpS`/`smroGet?`'s — `C`'s singleton
methods and `extend`s, up the superclass chain, **and then the metaclass tail** into `Class`'s
instance chain, which is the entailment §4.6 makes the seed respect. -/
inductive Port where
  | inst (c : String)
  | cls (c : String)
deriving BEq, DecidableEq, Repr, Inhabited

/-- Facts that grow: everything the checker learns as it walks the program in order.

The four fields are unchanged from the old flat `Ctx`; what changed is that they are now
together, with one discipline, and reported out of a derivation rather than reconstructed by
`JudgeSeq.cons`. -/
structure Pos where
  classes : CTable
  defs : DefTable
  /-- The **constant** environment (tier 13), keyed by absolute path (`"::LIMIT"`). Carried
      unchanged into every method body, which is the whole reason it is here rather than in
      `Env` — see §Constants below `Ctx.inCtor` for the three facts that force this
      placement. -/
  consts : Env
  /-- The absolute keys `private_constant` has hidden (tier 13d). Read by `Judge.constPath`
      and by nothing else. -/
  privConsts : List String
  /-- Retain the top-level receiver's heap/dispatch world across other activations. -/
  mainWorld : Bool := false
  /-- Classes proved to allocate plain objects, independently of method/initializer rows. -/
  plainAlloc : List String := []
deriving Inhabited

/-- Facts that shrink: what the program provably does **not** provide.

`noMethod` is keyed by a receiver **port** (§4.5, §4.6) rather than by a bare name, because
Ruby has more than one lookup relation and "is this name free?" has a different answer per
receiver. `(p, n) ∈ noMethod` means *nothing on `p`'s chain provides `n`* — which subsumes four
encodings that used to be separate: `nameFree`, `mroGet? … = none`, `smroGet? … = none`, and
`MissFree`'s `method_missing`.

**Seeded whole-program** (`negSeed`), not built up: a `def` buried in an expression is still a
`def`, and a table reconstructed from statement syntax cannot see it (§F20). Forgetting to seed
a name is conservative (a rule declines); forgetting to *remove* one is unsound, so the fragile
step lives at one place that sees all the syntax. -/
structure Neg where
  /-- The ports the seed enumerated. A port outside this list is unseeded, so a rule asking
      about it declines — the conservative direction §2.2 names. -/
  ports : List Port
  noMethod : List (Port × String)
  /-- Every method name the program declares **anywhere**, on any port. The coarse belt is its
      complement: `nameFree`'s old question, asked over the whole program instead of over the
      already-declared tables, for the rules that have no receiver type to hand.

      Stated as the *declared* set rather than the free one on purpose. The free set would have
      to be enumerated against a name list, and a name missing from that list would read as
      "free" — the unsound direction. A name missing from `declared` is one the program does not
      declare, which is the fact itself. -/
  declared : List String
  /-- A reflective declarer this pre-pass cannot read — `define_method` with a computed name,
      `define_singleton_method` with one. Nothing is free at such a program, and saying so with
      a flag is what keeps the two lists above meaning "and nothing more". -/
  unpinned : Bool
  /-- **The whole program's class table**, `extendClasses` folded over every `class`/`module`
      node wherever written. Read only by the **negative** guards §F9 needs — `isANoOk` and
      `mixinFreeChain`, which ask whether anything *anywhere* disturbs a builtin ancestor chain.
      The *positive* half of narrowing still reads `κ.classes`, the already-declared table, and
      the split is the point: a chain is broken by a class declared later just as much as by one
      declared earlier, while a constant not yet assigned resolves nowhere and raises.

      Asking it whole-program is **strictly more conservative** — a bigger table can only make
      `mixinFreeChain`/`noDeclaredBelow` answer `false`, i.e. refuse more refinements — so it
      cannot admit anything the per-point table refused. What it buys is that the guard is
      *invariant* under `Ctx.afterStmt`, which is what `StateOk`'s down-transport needs and what
      `context-splitting.md` §3 assumed without it. -/
  wholeCls : CTable
  /-- Every constant **name** the program binds anywhere. `coreConstFreeN`'s complement, and it
      is here for `wholeCls`'s reason: `coreConstFree` read `constGet? κ`, which grows, so the
      guard it feeds was antitone in `Pos`. -/
  boundConsts : List String
  /-- No constant of this absolute path is bound anywhere in the program. Not yet consumed by
      any rule — the cref work (§7.2) is what needs it — and seeded empty. -/
  freeConsts : List String
deriving Inhabited

/-- Lexical scope: rebound on entry to a body, never reported out.

Neither a positive fact about the heap nor a negative one. `asms` is here by §7.3's decision —
it is a conditional *assumption*, not a guarantee, and `Ctx.inMethod` already keeps it across a
body entry for a reason that is about scope. -/
structure Scope where
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
  /-- The assumptions in force, grown at a call site being discharged (`Judge.callDef`). -/
  asms : AsmTable
  /-- The ordinary `main` receiver world, shared by top level and its method activations.
      False imposes no runtime restriction; changing this flag requires state transport. -/
  runtimeMain : Bool := false
  /-- Ordinary lexical class owner, shared by a class body and its method activations.
      This is independent of the receiver type; `none` imposes no class-scope requirement. -/
  runtimeClass : Option String := none
  /-- Unmentioned self ivars are known to read as nil. Ordinary open instance annotations
      do not provide this fact; fresh initialization does. -/
  closedIvars : Bool := true
deriving Inhabited

/-- The judgment's non-local state, in three disciplines. -/
structure Ctx where
  pos : Pos
  neg : Neg
  scope : Scope
deriving Inhabited

/-- Open receiver annotations say nothing about unmentioned fields. -/
def Ctx.ivarReadTy (κ : Ctx) (I : Ty) (x : String) : Ty :=
  (ivarGet? I x).getD (if κ.scope.closedIvars then .nilT else .any)

/-! ### Field accessors

`Ctx.classes` and friends are `abbrev`s onto the sub-structures, so every `κ.classes` in the
checker, the rules and the proofs reads exactly as it did before the split and still reduces by
`rfl`. Only the *writers* — the sixteen `{ κ with … }` sites — had to move, and they moved to
the four named updaters below. -/
@[reducible] def Ctx.classes (κ : Ctx) : CTable := κ.pos.classes
@[reducible] def Ctx.defs (κ : Ctx) : DefTable := κ.pos.defs
@[reducible] def Ctx.consts (κ : Ctx) : Env := κ.pos.consts
@[reducible] def Ctx.privConsts (κ : Ctx) : List String := κ.pos.privConsts
@[reducible] def Ctx.ports (κ : Ctx) : List Port := κ.neg.ports
@[reducible] def Ctx.noMethod (κ : Ctx) : List (Port × String) := κ.neg.noMethod
@[reducible] def Ctx.declared (κ : Ctx) : List String := κ.neg.declared
@[reducible] def Ctx.negUnpinned (κ : Ctx) : Bool := κ.neg.unpinned
@[reducible] def Ctx.wholeCls (κ : Ctx) : CTable := κ.neg.wholeCls
@[reducible] def Ctx.boundConsts (κ : Ctx) : List String := κ.neg.boundConsts
@[reducible] def Ctx.freeConsts (κ : Ctx) : List String := κ.neg.freeConsts
@[reducible] def Ctx.frame (κ : Ctx) : Option Frame := κ.scope.frame
@[reducible] def Ctx.closures (κ : Ctx) : ClosTable := κ.scope.closures
@[reducible] def Ctx.blockTy (κ : Ctx) : Option Ty := κ.scope.blockTy
@[reducible] def Ctx.selfTy (κ : Ctx) : Option Ty := κ.scope.selfTy
@[reducible] def Ctx.asms (κ : Ctx) : AsmTable := κ.scope.asms

/-- Push an assumption (`Judge.callAsm`/`callDef`/`vcallDef`). -/
@[reducible] def Ctx.pushAsm (κ : Ctx) (a : Asm) : Ctx :=
  { κ with scope := { κ.scope with asms := a :: κ.scope.asms } }

/-- Re-point the running method's definition site (`super`). -/
@[reducible] def Ctx.withFrame (κ : Ctx) (f : Option Frame) : Ctx :=
  { κ with scope := { κ.scope with frame := f } }

/-- Bind the implicit block a body was entered with (`Judge.callDefBlk`). -/
@[reducible] def Ctx.withBlockTy (κ : Ctx) (t : Option Ty) : Ctx :=
  { κ with scope := { κ.scope with blockTy := t } }

/-- Fill in the whole-program block table (`Ctx.withBlocks`, `Ratchet/Validate.lean`). -/
@[reducible] def Ctx.withClosures (κ : Ctx) (K : ClosTable) : Ctx :=
  { κ with scope := { κ.scope with closures := K } }


/-! ### Seeding `Neg` (`context-splitting.md` §2.2, §4.5, §4.6)

`Neg` is not built up as the checker walks; it is **seeded by a whole-program pre-pass**, the
way `Ctx.closures` already is. That is what closes `found-issues.md` §F20: a `def` buried in an
expression is still a `def`, and a table reconstructed from *statement* syntax by
`Ctx.afterStmt` cannot see it, so every premise that read absence as a miss in that table
believed a name was unclaimed when it was not.

The polarity of the mistake is what makes a pre-pass the right shape. **Forgetting to seed a
name is conservative** — the rule that wanted the fact declines — while forgetting to *remove*
one is unsound. So the fragile step lives at one place that sees all the syntax, instead of at
every rule that might declare something.

Three pieces:

1. `negEmit` — walk the whole program and emit one `(Port, name)` for every declaration,
   *wherever* it is written. The site is carried down, so a `def` nested in a method body of
   `class C` lands on `inst C` and not on `Object`, which is both correct and the precision
   §10.1 measured as paying for the seeding.
2. `negWild` — the declarations whose port cannot be pinned (`def obj.m` for an `obj` that is
   not the enclosing `self`, `define_singleton_method`, a computed `define_method` name). These
   remove the name from **every** port; §4.6 argues that is the only sound answer available,
   since `Ty.inst` carries no object identity.
3. `negSeed` — the grid, closed under both chains of §4.6. -/

/-- The method names a rule ever asks `Neg` about. A name absent from this list is simply never
seeded, so a rule asking about it fails its premise — the conservative direction. -/
def negNames : List String :=
  ["lambda", "proc", "method_missing", "is_a?", "===", "nil?", "raise", "to_s", "class", "x",
   "new", "call"]

/-- The metaclass tail of §4.6: once a class object's singleton chain is exhausted, `C.foo`
falls through to these classes' **instance** methods. So `(cls C, n)` may only be seeded when
none of them declares `n` either — which is what makes the seed strictly finer than the
`nameFree κ "to_s"` belt §F7 needed, rather than merely different. -/
def metaTail : List String := ["Class", "Module", "Object", "Kernel", "BasicObject"]

/-- The class objects the seed enumerates. Anything outside this list is unseeded, so a rule
asking about it declines. -/
def negOwnerNames (C : CTable) : List String :=
  ("Object" :: "Proc" :: "Regexp" :: "Range" :: metaTail ++ builtinClsNames) ++ C.map (·.name)

/-- One declaration, at the port it lands on. -/
abbrev NegEmit := Port × String

/-- What one pass over a subexpression yields: the declarations it performs, the names whose
port it could not pin, and every `class`/`module` node it contains — the last so that the
**whole-program** class table can be folded from them, since `Ctx.afterStmt`'s version sees
only top-level statements and that is the other half of §F20. -/
structure NegAcc where
  emits : List NegEmit
  wild : List String
  decls : List Expr
  /-- Every constant **name** bound, wherever written. -/
  consts : List String

instance : Append NegAcc where
  append a b := ⟨a.emits ++ b.emits, a.wild ++ b.wild, a.decls ++ b.decls, a.consts ++ b.consts⟩

def NegAcc.empty : NegAcc := ⟨[], [], [], []⟩

/-- The site a `def` written here installs onto: the lexically enclosing class or module, or
`Object` at top level. Carried down through method bodies and blocks, because that is what
Ruby's *cref* does — `class C; def a; def b; end; end; end` makes `b` an instance method of
`C`. -/
abbrev NegSite := String

/-- The instance-method names an `attr_*` call declares. `attr_writer`/`attr_accessor` also
declare the `name=` setter. -/
def attrNames (s : NegSite) (m : String) : List Expr → List NegEmit
  | [] => []
  | .sym n :: rest =>
    let setter := if m == "attr_reader" then [] else [(Port.inst s, n ++ "=")]
    (Port.inst s, n) :: setter ++ attrNames s m rest
  | _ :: rest => attrNames s m rest

mutual

/-- Every declaration the program performs, with the port it lands on. Recurses into **every**
expression position, which is the whole point (§F20). -/
def negEmit (s : NegSite) : Expr → NegAcc
  | .def' n _ body => ⟨[(.inst s, n)], [], [], []⟩ ++ negEmit s body
  -- `def self.m` inside `class C` is a singleton method of `C`. Anywhere else — a `def obj.m`
  -- on some other receiver, or a `def self.m` at top level, where `self` is `main` — the port
  -- is not expressible (`Ty.inst` carries no object identity), so §4.6's uniform answer: the
  -- name leaves every port.
  | .defs recv n _ body =>
    (match recv with
     | .self' => if s == "Object" then ⟨[], [n], [], []⟩ else ⟨[(.cls s, n)], [], [], []⟩
     | _ => ⟨[], [n], [], []⟩) ++ negEmit s recv ++ negEmit s body
  | e@(.class' n sup body) =>
    ⟨[], [], [e], []⟩ ++ negEmitOpt s sup ++ negEmit n body
  | e@(.module' n body) => ⟨[], [], [e], []⟩ ++ negEmit n body
  -- A `class << obj` body declares singleton methods on an object the checker cannot name, so
  -- every name it declares leaves every port.
  | .sclass obj body =>
    let inner := negEmit s body
    ⟨[], inner.emits.map (·.2), [], []⟩ ++ negEmit s obj ++ inner
  | .alias' nw _ => ⟨[(.inst s, nw)], [], [], []⟩
  | .undef ns => ⟨[], ns, [], []⟩
  | .send recv m args blk =>
    let base := negEmitOpt s recv ++ negEmitAll s args ++ negEmitOpt s blk
    -- The reflective declarers. A literal-symbol name is as pinnable as a `def`; a computed
    -- one is not, and there is nothing honest to do with it but drop every name — which the
    -- `""` marker does, by emptying the seed.
    if m == "attr_reader" || m == "attr_accessor" || m == "attr_writer" then
      ⟨attrNames s m args, [], [], []⟩ ++ base
    else if m == "define_method" then
      (match args with
       | [.sym n] => ⟨[(.inst s, n)], [], [], []⟩
       | _ => ⟨[], [""], [], []⟩) ++ base
    else if m == "alias_method" then
      (match args with
       | [.sym nw, _] => ⟨[(.inst s, nw)], [], [], []⟩
       | _ => ⟨[], [""], [], []⟩) ++ base
    else if m == "define_singleton_method" then
      (match args with
       | .sym n :: _ => ⟨[], [n], [], []⟩
       | _ => ⟨[], [""], [], []⟩) ++ base
    else base
  | .seq es => negEmitAll s es
  | .vasgn _ _ e => negEmit s e
  | .casgn n e => ⟨[], [], [], [n]⟩ ++ negEmit s e
  | .cpathAsgn b n e => ⟨[], [], [], [n]⟩ ++ negEmitOpt s b ++ negEmit s e
  | .cpath b _ => negEmitOpt s b
  | .array es => negEmitAll s es
  | .hash ps => negEmitPairs s ps
  | .block _ _ body => negEmit s body
  | .yield' args => negEmitAll s args
  | .blockpass e => negEmitOpt s e
  | .if' c t e => negEmit s c ++ negEmit s t ++ negEmitOpt s e
  | .while' c body => negEmit s c ++ negEmit s body
  | .dowhile body c => negEmit s body ++ negEmit s c
  | .for' _ coll body => negEmit s coll ++ negEmit s body
  | .begin' body rescues els ens =>
    negEmit s body ++ negEmitRescues s rescues ++ negEmitOpt s els ++ negEmitOpt s ens
  | .super' args blk => negEmitAll s args ++ negEmitOpt s blk
  | .zsuper blk => negEmitOpt s blk
  | .ret e => negEmitOpt s e
  | .brk e => negEmitOpt s e
  | .nxt e => negEmitOpt s e
  | .splat e => negEmitOpt s e
  | .defined e => negEmit s e
  | .kwargs es => negEmitKw s es
  -- `class A::B` / `module A::B` — the base is an expression and the body declares under `B`.
  -- The node itself is **not** offered to `extendClasses`, which does not read these shapes; a
  -- class it cannot read is a class no rule can use, and the declarations inside it are still
  -- emitted, which is the conservative direction.
  | .scopedClass b n body => negEmitOpt s b ++ negEmit n body
  | .scopedModule b n body => negEmitOpt s b ++ negEmit n body
  | _ => NegAcc.empty

def negEmitAll (s : NegSite) : List Expr → NegAcc
  | [] => NegAcc.empty
  | e :: es => negEmit s e ++ negEmitAll s es

def negEmitOpt (s : NegSite) : Option Expr → NegAcc
  | none => NegAcc.empty
  | some e => negEmit s e

def negEmitPairs (s : NegSite) : List (Expr × Expr) → NegAcc
  | [] => NegAcc.empty
  | (k, v) :: ps => negEmit s k ++ negEmit s v ++ negEmitPairs s ps

def negEmitKw (s : NegSite) : List KwEntry → NegAcc
  | [] => NegAcc.empty
  | .pair _ v :: es => negEmit s v ++ negEmitKw s es
  | .dyn k v :: es => negEmit s k ++ negEmit s v ++ negEmitKw s es
  | .splat e :: es => negEmit s e ++ negEmitKw s es

def negEmitRescues (s : NegSite) :
    List (List Expr × Option (TargetKind × String) × Expr) → NegAcc
  | [] => NegAcc.empty
  | (cls, _, body) :: rs => negEmitAll s cls ++ negEmit s body ++ negEmitRescues s rs

end


/-! #### Closing the seed under the two chains (§4.6)

A raw emission says where a declaration *lands*; a `Neg` fact is about a whole **chain**. The
two are joined here, and the closure is done **at seed time** rather than re-checked per rule —
which is §10.4's resolution: the pre-pass sees the entire static hierarchy (superclasses,
`include`, `prepend`, `extend`), so `Coherent` modulo inheritance holds by construction. -/

/-- The instance lookup chain of `c` under the whole-program table, plus `Object` — which is on
every instance chain and is where a top-level `def` lands. -/
def negInstChain (C : CTable) (c : String) : List String :=
  ((mroList? C c).getD [c]) ++ ["Object"]

/-- The class object's own chain: `c` and its superclasses, walked with `C.length` fuel the way
`lookupUpS` does. -/
def negSingChain (C : CTable) : Nat → String → List String
  | 0, _ => []
  | k + 1, n =>
    n :: (match clsGet? C n with
          | some c => match c.super? with
                      | some sn => negSingChain C k sn
                      | none => []
          | none => [])

/-- Does any emission put `n` on `inst c`'s chain? Also reads each chain entry's `prepends`
and `includes`, which `mroList?` already folds in, so this is a lookup rather than a walk. -/
def negInstHit (C : CTable) (E : List NegEmit) (c n : String) : Bool :=
  (negInstChain C c).any (fun a => E.contains (.inst a, n))

/-- Does any emission put `n` on `cls c`'s chain — the singleton chain, the modules each of its
entries `extend`s, **or the metaclass tail**? The third disjunct is §F7's belt made precise:
today's `nameFree κ "to_s"` goes false as soon as any class anywhere declares `to_s`; this asks
only about `Class`/`Module`/`Object`/`Kernel`/`BasicObject`. -/
def negClsHit (C : CTable) (E : List NegEmit) (c n : String) : Bool :=
  let chain := negSingChain C (C.length + 1) c
  chain.any (fun a =>
    E.contains (.cls a, n) ||
    (match clsGet? C a with
     | some cl => cl.extended.any (fun mm => negInstHit C E mm n)
     | none => false)) ||
  metaTail.any (fun t => negInstHit C E t n)

/-- The whole-program class table: `extendClasses` folded over **every** `class`/`module` node
`negEmit` found, wherever written. -/
def wholeClasses (ds : List Expr) : CTable := ds.foldl extendClasses []

/-- The `Neg` a program is checked under. -/
def negSeed (p : Expr) : Neg :=
  let acc := negEmit "Object" p
  let C := wholeClasses acc.decls
  let E := acc.emits
  -- A declaration whose name could not be pinned to a port removes that name everywhere; the
  -- empty string is `negEmit`'s marker for "a reflective declarer with a computed name", which
  -- nothing can be sound about, so it empties the seed.
  if acc.wild.contains "" then ⟨[], [], [], true, C, acc.consts, []⟩ else
  let names := negNames.filter (fun n => !acc.wild.contains n)
  let owners := negOwnerNames C
  let ports := owners.flatMap (fun c => [Port.inst c, Port.cls c])
  let noMethod :=
    names.flatMap (fun n =>
      owners.flatMap (fun c =>
        (if negInstHit C E c n then [] else [(Port.inst c, n)]) ++
        (if negClsHit C E c n then [] else [(Port.cls c, n)])))
  -- The coarse belt, whole-program: every name the program declares anywhere, at any port or
  -- at none. This is what `nameFree` used to read off the already-declared tables.
  ⟨ports, noMethod, E.map (·.2) ++ acc.wild, false, C, acc.consts, []⟩

/-! #### Reading `Neg`

Three queries, and the shape §4.4 argues for: every one is a **lookup**, not a whole-table
scan. A miss in a positive table is a claim about that table's completeness; a hit in `Neg` is
a fact of its own. -/

/-- **Is `n` free on this receiver port?** The keyed query (§4.5). -/
def portFree (κ : Ctx) (p : Port) (n : String) : Bool := κ.noMethod.contains (p, n)

/-- **Is `n` declared nowhere in the program?** The coarse belt, for a rule with no receiver
type to hand — `Judge.bareName`, `lambdaLit`, `raiseCls`, and the narrowing guards, all of
which are implicit-self sends whose `self` this judgment does not always type.

This is `nameFree`'s question, and the only change is *where* it is asked: over the whole
program, so a `def` written anywhere at all answers it (`found-issues.md` §F20), rather than
over the tables `Ctx.afterStmt` reconstructed from statement syntax. -/
def nameFreeN (κ : Ctx) (n : String) : Bool := !κ.negUnpinned && !κ.declared.contains n

/-- The receiver ports a type denotes, or `none` where the type pins no class — `.any`, an
arrow, an ivar spine. `none` is not "no ports": a rule asking about an unpinned receiver gets
`false` and declines. -/
def tyPorts? : Ty → Option (List Port)
  | .int => some [.inst "Integer"]
  | .float => some [.inst "Float"]
  | .bool => some [.inst "TrueClass", .inst "FalseClass"]
  | .nilT => some [.inst "NilClass"]
  | .sym => some [.inst "Symbol"]
  | .cls n => some [.inst n]
  | .clsOf n => some [.cls n]
  | .arrayOf _ => some [.inst "Array"]
  | .hashOf _ _ => some [.inst "Hash"]
  | .inst n _ => some [.inst n]
  | .clos _ _ _ => some [.inst "Proc"]
  | .never => some []
  | .nilable τ => (tyPorts? τ).map (fun ps => .inst "NilClass" :: ps)
  | .union σ τ =>
    match tyPorts? σ, tyPorts? τ with
    | some a, some b => some (a ++ b)
    | _, _ => none
  | .sameAs _ τ => tyPorts? τ
  | _ => none

/-- **Is `n` free on every port a receiver of type `σ` can have?** -/
def tyFree (κ : Ctx) (σ : Ty) (n : String) : Bool :=
  match tyPorts? σ with
  | some ps => ps.all (fun p => portFree κ p n)
  | none => false

/-- **The frame-sensitive records in `Ctx` that an assignment can invalidate.**

`Ratchet/Ty.lean` §Stale closure captures fixes `Judge.vasgn` by *rewriting* the outgoing
`Env` and ivar spine (`killClosOver`/`killClosOverSpine`). Three `Ctx` fields can hold a
`Ty.clos` too — `selfTy` (its ivar spine may name one), `blockTy` (it *is* one) and `consts` —
and `Ctx` is an **input** to every rule: no rule rewrites it, so no rule can widen them. So
they become a *premise* instead: the rule applies only where they record nothing about the
assigned name that the assignment would falsify.

Sound rather than precise, and the imprecision is namespaced. A method frame captures nothing,
so an assignment inside a method body cannot reach the frame `blockTy`'s closure captured;
this premise nevertheless refuses the case where the two happen to use the same *name*. The
alternative — a `StateOk` component stating frame-chain disjointness — is a bigger change to
the semantic side for precision no rung has asked for; recorded in `found-issues.md` §F1
rather than built. -/
def capStaleCtx (x : String) (τ : Ty) (κ : Ctx) : Bool :=
  capStale x τ (κ.selfTy.getD .never) || capStale x τ (κ.blockTy.getD .never) ||
    κ.consts.any (fun p => capStale x τ p.2)

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
  { κ with scope := { κ.scope with selfTy := some σ, frame := some ⟨selfClsName σ, dc, m⟩ } }

/-- Entering a body whose `self` this judgment declines to type — `initialize` (see
`Judge.newInst`) — but whose *definition site* still has to be recorded, because the body may
call `super`. -/
def Ctx.inCtor (κ : Ctx) (rc dc m : String) : Ctx :=
  κ.withFrame (some ⟨rc, dc, m⟩)

/-! ### Constants (tier 13)

A constant is a **binding**, and the three facts that decide where it lives are:

1. its type is not syntactic — `LIMIT = compute` needs the judgment to know what `compute`
   answers, so a constant table cannot be built by a syntactic pre-pass the way `CTable`
   and `DefTable` are;
2. it is written once and read from *everywhere afterwards*, including from inside method
   bodies whose local environment is the fresh, parameters-only one `paramEnv` builds — so
   it cannot live in `Env`, which is exactly the state a call rule replaces;
3. but it is still **order-sensitive**: `X + 1; X = 10` raises `NameError`, so a
   whole-program table would certify a program that fails.

`Ctx.consts` satisfies all three at once. It is in `Ctx`, so every body-entering rule
(`Ctx.inMethod`/`inCtor`, and the call rules' `{κ with …}`) carries it into the callee for
free — which is right, because a constant assigned before the call really is assigned when
the body runs. And it grows at `JudgeSeq.cons`, which is the one rule that knows statement
order, so fact 3 holds for the same reason `foo(); def foo; end` has no derivation.

The price is that `Ctx.afterStmt` now needs the statement's **type**, since that is what a
`casgn` binds. That is available in `JudgeSeq.cons` (it is the `σ` the first premise
produces) and in `chkSeq`, and it is the only change to a rule already on file.

Keys are the constant's **absolute path** (`"::LIMIT"`, `"::Box::SIZE"`), which is Ruby's own
notation for one and keeps the namespace visibly disjoint from `Env`'s locals — no local can
contain a colon. -/
def constPaths (κ : Ctx) (n : String) : List String :=
  match κ.frame with
  | some f => [constKeyIn f.defClass n, constKey n]
  | none => [constKey n]

/-- What a constant read resolves to, or `none` if the program has not assigned it — in
which case there is no rule and the read is rejected, which is what fact 3 above buys.

**Resolution is lexical, innermost first** (tier 13b): inside a method body, a bare `SIZE`
means `Box::SIZE` if the running method was *declared* in `Box`, and the top-level `SIZE`
otherwise. `Frame.defClass` is exactly the right name to ask — it is where the method was
found, which for a method declared with `def` inside `class Box` is `Box`, and for an
inherited one is the ancestor whose body the `def` was written in. Both are Ruby's lexical
cref for that `def`.

Outside any method (`frame = none`) only the top-level path is tried, which is why
`class Box; SIZE = 3; end; SIZE` is rejected — Ruby raises `NameError` for it. -/
def constGet? (κ : Ctx) (n : String) : Option Ty :=
  (constPaths κ n).findSome? (fun k => envGet? κ.consts k)

/-- The constants a statement binds. `envSet` rather than a cons because Ruby's
re-assignment of a constant is a warning, not an error, and the *later* type is the live one.

A `class`/`module` statement binds the constants in its **body** (tier 13b), and those get
their types from `constLitTy?` — see §A class body's constants for why that is a syntactic
function and what makes it sound. -/
def extendConsts (S : Env) : Expr → Ty → Env
  | .casgn n _, τ => envSet S (constKey n) τ
  -- Tier 13c: `M::X = 4`. The base is matched *syntactically* here, which is why
  -- `Judge.cpathAsgn` is stated at the same syntax: the two have to agree about the key, and
  -- a base this pattern does not read simply binds nothing (conservative).
  | .cpathAsgn (some (.const owner)) n _, τ => envSet S (constKeyIn owner n) τ
  -- Tier 13e: and the constants of anything nested inside it, at their qualified owners.
  | .class' n _ body, _ =>
    addNestedConsts (addClassConsts S n (bodyConsts body)) nestFuel n (bodyNested body)
  | .module' n body, _ =>
    addNestedConsts (addClassConsts S n (bodyConsts body)) nestFuel n (bodyNested body)
  | _, _ => S

/-- **What a constant assignment owes the tables that already describe the name**
(`found-issues.md` §F18).

`Ctx.afterStmt` records a constant's type from a **top-level `casgn` statement**, and
`extendConsts` matches only that shape — so an assignment *buried* inside a larger expression
(`y = (X = "s")`) rebinds the constant at run time while `κ.consts` still carries the old type.
`Judge.casgn` had no premise at all and its docstring called the invisibility "conservative, in
the direction that costs a rung rather than soundness". It was not: `X = 1; y = (X = "s"); X + 1`
was certified `Integer` against a `TypeError`, and `y = (String = 5); String.new` is the same
hole through `constBuiltin` instead of `constEnv`.

**Agreement, not absence** — the same shape §F17 settled on, and for the same reason: the
first assignment of a name resolves nowhere yet, so absence is what the *common* case has, and
a re-assignment at the type already recorded changes nothing anyone read. What is refused is a
rebinding the tables would then be wrong about: a different type, a declared class, a builtin
class, or an exception class. -/
def constAsgnOk (κ : Ctx) (n : String) (τ : Ty) : Bool :=
  match constGet? κ n with
  | some σ => σ == τ
  | none =>
    (clsGet? κ.classes n).isNone && !builtinClsNames.contains n && !excName? κ.classes n

/-- `κ` after performing statement `e`, which produced a value of type `τ`: both syntax
tables grow, the constant table grows if `e` was a `casgn`, nothing else changes. Used only
by `JudgeSeq.cons`, which is the only rule that knows about statement order.

`τ` is used by `extendConsts` alone; every other component of the result is syntactic. -/
def Ctx.afterStmt (κ : Ctx) (e : Expr) (τ : Ty) : Ctx :=
  { κ with pos := { classes := extendClasses κ.classes e, defs := extendDefs κ.defs e,
                     consts := extendConsts κ.consts e τ,
                     privConsts := extendPrivConsts κ.privConsts e } }

/-- Is the method name `m` **unclaimed by the program** — no top-level `def`, and no class or
module in the table declaring it as an instance or singleton method?

Read by `Judge.lambdaLit` (`found-issues.md` §F2). `lambda { … }` is an *implicit-self send*,
and in CRuby a toplevel `def lambda` installs a private method **on `Object`** while `Kernel`
is included *in* `Object` — so the user's definition shadows `Kernel#lambda` and
`f = lambda { 1 }` binds `5`, not a Proc. The rule concluded `.clos` unconditionally, which is
how `def lambda; 5; end; f = lambda { 1 }; f.call + 1` came to be certified `Integer` against a
`NoMethodError`.

Deliberately coarse: it asks whether *any* class declares the name, not whether the class
`self` belongs to does. Sharpening it means reading `κ.selfTy` and the ancestor chain, and the
imprecision costs nothing any rung wants — no program in this corpus names a method `lambda` or
`proc`. -/
def nameFree (κ : Ctx) (m : String) : Bool :=
  (κ.defs.find? (·.name == m)).isNone &&
  κ.classes.all (fun c => (c.methods.find? (·.name == m)).isNone &&
                          (c.smethods.find? (·.name == m)).isNone)

/-- `paramEnv` for a call that **carries a block**. Same walk, plus one case: a
`&b` parameter (`Param.block`) consumes not an argument but the block itself.

`blk` is `none` when the call passes no block, and then `&b` binds `.nilT` — which is exactly
Ruby (`def run(&b); b; end; run` is `nil`), and also exactly why the binding cannot be
skipped: `b` is in scope either way. A `&b` parameter is required to come **last**, which is
not enforced here because the parser already guarantees it. -/
def paramEnvB (blk : Option Ty) (ps : List Param) (τs : List Ty) : Option Env :=
  paramBind blk ps τs []

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
  /-- **`inject` over a provably empty receiver** (tier 14b), where the block's return type is
      unconstrained.

      `arrayOf .never` says "every element of this array does not return a value", and `.never`
      is uninhabited — so an array of that type **has no elements**, the block never runs, and
      the result is the seed whatever the block would have returned. That is the whole argument,
      and it is about the *receiver's element type*, not about `ρ`: keying it on `ρ = .never`
      would be a different and much weaker claim.

      What needs it: `def total(*ns); ns.inject(0) { |a, b| a + b }; end; total()`. A rest
      parameter with no arguments left is `arrayOf (elemTy []) = arrayOf .never`, so the block
      is judged with `b : .never`, `a + b` is `.never` by strictness, and the general `inject`
      row's `ρ = α` fails on a call that cannot go wrong. -/
  | injectEmpty {α ρ : Ty} : IterSig "inject" .never [α] [α, .never] ρ α
  -- ### Tier 17's iterators
  /-- `xs.any? { … }` / `xs.all? { … }` → `Bool`. The block's result is only tested for
      truthiness, which never raises, so `ρ` is unconstrained — `select`'s reason. -/
  | anyP {τ ρ : Ty} : IterSig "any?" τ [] [τ] ρ .bool
  | allP {τ ρ : Ty} : IterSig "all?" τ [] [τ] ρ .bool
  /-- `xs.each_with_index { |v, i| … }` → self. The **first two-parameter iterator whose second
      parameter is not an accumulator**: `inject` binds `[α, τ]`, this binds `[τ, .int]`, and the
      `.int` is the only thing in the table that comes from neither the receiver nor the
      arguments. -/
  | eachWithIndex {τ ρ : Ty} : IterSig "each_with_index" τ [] [τ, .int] ρ (.arrayOf τ)
  /-- `xs.flat_map { … }` → the concatenation, so the block must return an **array** and the
      result's element type is that array's. Ruby also accepts a non-array return (it is
      included as-is); that shape has no row, because the result would be a union of two element
      types and nothing consumes one. -/
  | flatMap {τ σ : Ty} : IterSig "flat_map" τ [] [τ] (.arrayOf σ) (.arrayOf σ)
  /-- `xs.filter_map { … }` → the block's **truthy** results, so the element type is
      `truthyTy ρ` — tier 12's refinement used on a result rather than in a branch, and the
      second row (with `compact`) whose result type is computed by one. Note it removes `false`
      as well as `nil`, which is why `truthyTy` rather than `nonNilTy`. -/
  | filterMap {τ ρ : Ty} : IterSig "filter_map" τ [] [τ] ρ (.arrayOf (truthyTy ρ))
  /-- `xs.find { … }` → an element **or nil**, because nothing may match. `ρ` unconstrained for
      `select`'s reason. -/
  | findFirst {τ ρ : Ty} : IterSig "find" τ [] [τ] ρ (mkNilable τ)

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
  { κ with scope := { κ.scope with selfTy := closSelf? σ, frame := none, blockTy := none } }

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

/-- **Does every spine in this type agree with `τ` about the instance variable `x`?** —
`found-issues.md` §F17's guard.

An `.inst n I` type carries a spine, and a spine entry for `x` is a claim about *some* object's
`@x`. An assignment to `self`'s `@x` invalidates such a claim when the object is `self` — which
the type cannot tell — so the check has to be conservative about *which* object and precise
about *what*: a spine that says nothing about `x` is untouched (the spine is a **lower bound**,
so an unmentioned ivar is unconstrained), and a spine that says `x : τ` is still right if the
value written is a `τ`. Only a spine that records a *different* type is refused.

Both halves matter for the corpus. Refusing every mention would reject every assignment inside
a method, because `κ.selfTy`'s own spine records the ivars; accepting every mention is
`corpus/240`, where `@a : Integer` is overwritten with a `String` while a local holds `self`.

Recursive through every constructor that can *contain* an `.inst` — `union`, `nilable`,
`arrayOf`, `hashOf`, `sameAs`, and the spines themselves. The arrow arms are exempt and a
`clos`'s two type components are not; see the note in `Judge.ivarAsgn`. -/
def ivarAgree (x : String) (τ : Ty) : Ty → Bool
  | .inst _ I => (match ivarGet? I x with | none => true | some ρ => ρ == τ) && ivarAgree x τ I
  | .union σ ν => ivarAgree x τ σ && ivarAgree x τ ν
  | .nilable ρ | .arrayOf ρ | .sameAs _ ρ => ivarAgree x τ ρ
  | .hashOf κ' ν => ivarAgree x τ κ' && ivarAgree x τ ν
  | .ivarCons n σ rest =>
    (n != x || σ == τ) && ivarAgree x τ σ && ivarAgree x τ rest
  -- **The arrow arms are fine, and the reason is `Later`.** An arrow's denotation is a claim
  -- about *future* runs, quantified over `Later`-futures of the machine, so it survives any
  -- change that relation admits — an ivar write included. A `clos` is not quantified: it reads
  -- the captured frame and creation `self` at *this* machine, so its two type components have
  -- to be checked.
  | .arrow0 _ | .arrowCons _ _ => true
  | .clos _ cap selfT => ivarAgree x τ cap && ivarAgree x τ selfT
  | _ => true

/-- The same over an environment, and over `κ.selfTy` — which records the running method's own
`self`, spine and all, and is therefore the *usual* place a mention appears. -/
def ivarAgreeEnv (x : String) (τ : Ty) (Γ : Env) : Bool :=
  Γ.all (fun p => ivarAgree x τ p.2)

def ivarAgreeSelf (x : String) (τ : Ty) : Option Ty → Bool
  | none => true
  | some σ => ivarAgree x τ σ

/-- **The incoming `self` spine, checked everywhere except at `@x` itself.**

The sixth place, and the one that is not context: `I'` is what the *judgment* has inferred
about `self`'s instance variables, and `SelfSpineOk` reads every entry of it through
`ivarOf … self`. An entry `@a : C[@x : Int]` describes an object that could *be* `self`
(`@a = self`), and then writing `@x` at a different type falsifies it.

The top-level `@x` entry is **exempt**, and it has to be: `ivarSet` replaces it with `τ`, so
its old type is not read after the write. Requiring agreement there instead of exempting it
would reject every type-changing reassignment — `if flag then @v = 1 else @v = "s"`, which is
the program that put `joinIvars` in `Ratchet/Ty.lean` in the first place. -/
def ivarAgreeIvars (x : String) (τ : Ty) : Ty → Bool
  | .ivarCons n σ rest => (n == x || ivarAgree x τ σ) && ivarAgreeIvars x τ rest
  | _ => true

/-- **Everything the context records that could hold a spine mentioning `@x`.** Five places,
and the list is not a guess: it is the `StateOk` components whose statement applies `denM` to a
type the *context* supplies — the environment, the right-hand side's own type, `self`'s type,
the block's type, and the constant table. The others read only the heap's shape, which an
instance-variable write leaves alone. -/
def ivarAsgnOk (κ : Ctx) (x : String) (τ : Ty) (Γ' : Env) (I' : Ty) : Bool :=
  ivarAgreeEnv x τ Γ' && ivarAgree x τ τ && ivarAgreeSelf x τ κ.selfTy &&
  ivarAgreeSelf x τ κ.blockTy && ivarAgreeEnv x τ κ.consts && ivarAgreeIvars x τ I'

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

/-- **A `return` is local to a lambda and not to a proc**, which is what `bodyResult` above
did not distinguish (`found-issues.md` §F19).

`lambda { return e }.call` evaluates `e` and hands it back to the caller — so rewriting the
body to `e` is exactly right, and `lambda-explicit-return` (rung 105) is that rung.
`proc { return e }.call` does something else entirely: the `return` returns from the
**enclosing method**, so the call never comes back at all and the *method's* value becomes
`e`'s. Typing the call as `e`'s type is then wrong twice over — the call has no type, and the
method's recorded return type is a lie.

`Judge.lambdaLit` is the only rule that turns a block literal into a callable `Ty.clos`, and it
admits `lambda` and `proc` alike, so this is the one place the distinction can be drawn without
adding a field to `Clos`. It is drawn as a **refusal**: a `proc` whose body is exactly
`return e` gets no type, so `closCall` never sees one and `bodyResult` stays sound where it is
still used.

Note the guard has to match `bodyResult`'s pattern and not merely mention `.ret`: a `return`
anywhere *other* than as the whole body has no rule of its own, so those bodies were already
untypeable and this refuses nothing new. -/
def procRetOk (m : String) (body : Expr) : Bool :=
  match body with
  | .ret (some _) => m == "lambda"
  | _ => true

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
def isANilPart (_C W : CTable) (cn : String) : Ty :=
  if ("NilClass" :: rootAncestors).contains cn then .nilT
  -- §F9 again, at `nil`: `class NilClass; include M; end` makes `nil.is_a?(M)` true, so the
  -- `.never` is only available when the context leaves that chain alone — and `isANoOk` is
  -- the same guard `isAAnswer`'s negative answer uses, which is what lets one component
  -- (`BaseChainsOk`) serve both
  else if isANoOk W ("NilClass" :: rootAncestors) then .never else .nilT

/-- …and to the else-branch, which is its complement. -/
def notANilPart (cn : String) : Ty :=
  if ("NilClass" :: rootAncestors).contains cn then .never else .nilT

/-- The values of `τ` that **are** a `cn`. -/
def isATy (C W : CTable) (cn : String) : Ty → Ty
  | .union σ τ => joinT (isATy C W cn σ) (isATy C W cn τ)
  | .nilable ρ => joinT (isANilPart C W cn) (isATy C W cn ρ)
  | τ => match isAAnswer C W cn τ with
    | some false => .never
    | _ => τ

/-- The values of `τ` that are **not** a `cn`. -/
def notATy (C W : CTable) (cn : String) : Ty → Ty
  | .union σ τ => joinT (notATy C W cn σ) (notATy C W cn τ)
  | .nilable ρ => joinT (notANilPart cn) (notATy C W cn ρ)
  | τ => match isAAnswer C W cn τ with
    | some true => .never
    | _ => τ

/-- The refinement the **then**-branch applies. -/
def refineThen (C W : CTable) : NarrowKind → Ty → Ty
  | .truthy, τ => truthyTy τ
  | .isNil, τ => isNilTy τ
  | .isA cn, τ => isATy C W cn τ

/-- The refinement the **else**-branch applies. -/
def refineElse (C W : CTable) : NarrowKind → Ty → Ty
  | .truthy, τ => falsyTy τ
  | .isNil, τ => nonNilTy τ
  | .isA cn, τ => notATy C W cn τ

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
def refineOne (C W : CTable) (k : NarrowKind) (thenSide : Bool) (Γ : Env) (x : String) : Env :=
  let refine := fun τ => if thenSide then refineThen C W k τ else refineElse C W k τ
  match envGet? Γ x with
  | none => Γ
  | some (.sameAs y τ) =>
    let Γ₁ := envSet Γ x (.sameAs y (refine τ))
    match envGet? Γ₁ y with
    -- §F15 applies here too: the target's binding is refined from its *stripped* type, and
    -- that refinement can be an alias for the same reason (a union with an alias member).
    | some ρ =>
      let ρ' := refine (stripAlias ρ)
      envSet Γ₁ y (if isAliasTy ρ' then ρ else ρ')
    | none => Γ₁
  -- **`found-issues.md` §F15**: the refinement must not *create* an alias claim. `refine` can:
  -- `falsyTy (union (sameAs y ρ) int)` is `joinT (sameAs y (falsyTy ρ)) never`, which is the
  -- `sameAs` — so refining a binding the environment describes as a **union** would record
  -- that `x` and `y` hold the same object, which the union never said. `EnvOk`'s alias
  -- conjunct is exactly that claim, and nothing in the judgment justifies it here (the alias
  -- *arm* above is the justified case, and it keeps the alias it was given). Declining to
  -- refine is the conservative answer, and it costs nothing measurable: the only way a
  -- `sameAs` reaches a union is a desugarer temporary joined across branches.
  | some τ =>
    let τ' := refine τ
    envSet Γ x (if isAliasTy τ' then τ else τ')

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

/-- Every name that appears in any `builtinAncestors` row. The chains the *positive* `is_a?`
answer reads, listed so `coreConstFree` can ask about all of them at once. -/
def coreChainNames : List String :=
  ["Integer", "Float", "NilClass", "Symbol", "String", "Hash", "Array",
   "Numeric", "Comparable", "Enumerable"] ++ rootAncestors

/-- **Does the context leave the core class *names* alone?** — §F10's guard, chain-side.

`constGet? κ cn = none` covers the name being **tested**. It does not cover the names the
static chain is written in, and those matter for the other direction: with `Foo = Object` in
the program, `"s".is_a?(Foo)` is *true* while `"Foo"` is in no chain, and with
`Comparable = Integer` the name in `String`'s own chain no longer denotes what the chain means
by it. The first is caught by the per-name guard (`Foo` is bound, so no narrowing); the second
is what this one is for. Blunt — any constant assignment to a core class name turns `.isA`
narrowing off program-wide — and blunt in the direction that costs rungs. -/
def coreConstFree (κ : Ctx) : Bool :=
  coreChainNames.all (fun n => (constGet? κ n).isNone)

/-- **The same guard, asked over the whole program** — `Neg.boundConsts` instead of
`constGet? κ`, for `Neg.wholeCls`'s reason and with the same trade. `constGet? κ` grows along
program order, so the guard it fed was **antitone in `Pos`** and `StateOk` could not be
transported back down across a statement that bound a constant
(`context-splitting.md` §12.2, `found-issues.md` §F21). Asking whether the name is bound
*anywhere* is invariant, and strictly more conservative: a program that rebinds a core class
name loses the refinement everywhere rather than only after the assignment. -/
def coreConstFreeN (κ : Ctx) : Bool :=
  coreChainNames.all (fun n => !κ.boundConsts.contains n)

/-- **`found-issues.md` §F10's guard: the name has to mean the class it names.**

`narrowCond?` reads the tested class out of the condition's **syntax** — `x.is_a?(Foo)` gives
`.isA "Foo"` — and `isAAnswer` then answers off `Foo`'s *name*. A constant is not its name:

```ruby
Foo = Integer
x = 5
if x.is_a?(Foo) then x + "s" end   # certified: "Foo" is not in Integer's static chain
```

so a `casgn` that aliases a class defeats every static answer about the aliased name, in the
`.never` direction that certifies anything. One condition covers it, and it is the one
`Judge.constCls`/`constBuiltin` already carry for reads: **the context binds no constant of
that name**. A name the context does not bind either resolves to the boot class of the same
name (which is what the static tables describe) or does not resolve at all — and then the
condition itself raises `NameError` and the branch never runs.

`.truthy`/`.isNil` need no guard: neither mentions a class. -/
def narrowNameOk (κ : Ctx) : NarrowKind → Bool
  -- **The tested name has to *be* a class.** `narrowCond?` reads it out of the condition's
  -- syntax, and the `C === x` shape puts it in the **receiver** position — where a non-class
  -- constant dispatches `===` to something else entirely (`String#===` is equality, not an
  -- ancestor test), so the refinement would be about the wrong question. `validate` cannot
  -- build such a derivation today (the `.const` rules type only class names, and a *user*
  -- constant is caught by the `constGet?` guard above), but the judgment quantifies over
  -- contexts and the *semantic* premise for the condition carries no typing — so the fact has
  -- to be stated. `nameFree κ "==="` is the companion: with the name unclaimed, `ClsQueryOk`
  -- says what `===` at a class object resolves to.
  | .isA cn =>
    !κ.boundConsts.contains cn && coreConstFreeN κ &&
    ((clsGet? κ.classes cn).isSome || builtinClsNames.contains cn) &&
    nameFreeN κ "===" && nameFreeN κ "is_a?" && nameFreeN κ "method_missing" &&
    -- and §F9's root-chain guard, which `isAAnswer`'s `.inst` arm consults
    mixinFreeChain κ.wholeCls rootAncestors
  -- **§F14**: `x.nil?` is a *dispatch*, and `nil?` is an ordinary method name. A program that
  -- redefines it moves the branch the refinement is attached to:
  -- `class NilClass; def nil?; false; end; end; x = nil; if x.nil? then 1 else x + 1 end`
  -- takes the **else** branch, where `nonNilTy .nilT` is `.never` — so everything in it is
  -- certified, and it runs `nil + 1`. `Judge.nilQuery` guards its own *typing* of `x.nil?`
  -- with `NilQSafe`, which is about the receiver's shape rather than the name; the narrowing
  -- needs the name, and `nameFree` is the same premise §F6 added for `is_a?`.
  | .isNil => nameFreeN κ "nil?" && nameFreeN κ "method_missing"
  | _ => true

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
def narrowEnvs (κ : Ctx) (c : Expr) (Γ : Env) : Env × Env :=
  match narrowCond? c with
  | some (.lvar, x, k, sides) =>
    if narrowNameOk κ k then
      (refineOne κ.classes κ.wholeCls k true Γ x,
       match sides with
       | .both => refineOne κ.classes κ.wholeCls k false Γ x
       | .thenOnly => Γ)
    else (Γ, Γ)
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
def narrowSpine (κ : Ctx) (c : Expr) (I : Ty) : Ty × Ty :=
  match narrowCond? c with
  | some (.ivar, x, k, sides) =>
    if narrowNameOk κ k then
      let τ := (ivarGet? I x).getD .nilT
      (ivarSet I x (refineThen κ.classes κ.wholeCls k τ),
       match sides with
       | .both => ivarSet I x (refineElse κ.classes κ.wholeCls k τ)
       | .thenOnly => I)
    else (I, I)
  | _ => (I, I)

/-! ## What a statement owes the context the sequence rule reports back down

`context-splitting.md` §3 prices "weaken an outgoing `P'` back to a smaller `P`" at "antitone,
one line", on the grounds that `PosOk` is a `∀`-over-a-set and a bigger set is a stronger claim.
Three of `StateOk`'s components are not that shape, and this predicate is what buys them:

* **`ConstsOk`/`ConstPathsOk`** — `extendConsts` is `envSet`, which **overwrites**. A statement
  that rebinds a constant at a different type falsifies the old claim outright, and one that
  binds a *qualified* key can shadow an unqualified one `constGet?` was resolving through the
  frame's cref. §10.3's "our facts are keyed and immutable-per-key" is exactly what `consts` is
  not: it is keyed and **mutable** per key.
* **`BaseChainsOk`** — three of its clauses are guarded by facts *about the context*
  (`coreConstFree`, `isANoOk`, and `constGet? cn = none`), and every one of them fires on
  **fewer** inputs as the context grows. So it is antitone exactly where `ClassesOk` is
  monotone. That is §1.1's opposite-variance problem again, surviving the polarity split
  because this time it is *inside* `Pos`.

Each clause is a decidable `Bool` at a concrete pair of contexts, discharged by `rfl` wherever
it is a premise — the same shape `Neg`'s premises have, for §10.1(1)'s reason. What it refuses
is a statement that rebinds a constant, shadows one through the cref, binds a **class** to a new
constant (§F10's `Foo = Integer` shape), rebinds a core class name, or declares a class below a
builtin base. `Judge.casgn`'s `constAsgnOk` (§F18) already refuses the first; no corpus program
does any of the rest, which is what makes this a premise rather than a loss.

The honest reading: this is the *residue* of §7.2. `consts` is not a `Pos` field — it neither
grows monotonically nor stays immutable per key — and the two facts `BaseChainsOk` guards on are
**negative** facts about the context ("no constant rebinds a core name", "no class is declared
below this base"), which by §2's own test belong in `Neg`, seeded whole-program the way
`noMethod` is. Until that edit window, this predicate names the gap and makes it checkable. -/

/-- Does this type denote a class *object*? `.clsOf` is the only arm that does, and §F10's
shape (`Foo = Integer`) is exactly a constant bound at one. -/
def isClsOfTy : Ty → Bool
  | .clsOf _ => true
  | _ => false

/-- The seven static ancestor chains `Denote/Sem/State.lean`'s `BaseChainsOk` is stated over,
without the boot ids — so that a `Ratchet`-side premise can talk about them. Kept here rather
than there because the *checker* is what has to discharge it. -/
def builtinChains : List (List String) :=
  [["Integer", "Numeric", "Comparable"] ++ rootAncestors,
   ["Float", "Numeric", "Comparable"] ++ rootAncestors,
   "NilClass" :: rootAncestors,
   ["Symbol", "Comparable"] ++ rootAncestors,
   ["String", "Comparable"] ++ rootAncestors,
   ["Hash", "Enumerable"] ++ rootAncestors,
   ["Array", "Enumerable"] ++ rootAncestors]

/-- **Everything `κ` claims about a machine, `κ'` still claims.**

Two families of clause, one per component that is not simply a `∀`-over-a-growing-set:

* **constants** (`ConstsOk`, `ConstPathsOk`) — every binding survives at the same type, and no
  new key shadows one `constGet?` was resolving through the frame's cref.
* **the class table's *antecedents*** (`DeclClassOk`) — `smroGet? … "new" = none`,
  `ctorGet? … = none`, `ancestors? … = some ch` and `mixinFreeChain` all guard clauses of that
  component, and all four fire on fewer inputs as the table grows. Stated one-directionally,
  since only "the goal's antecedent implies the hypothesis's" is needed.

`BaseChainsOk`'s three guards are **not** here: they were moved to `Neg` (`wholeCls`,
`boundConsts`), which `Ctx.afterStmt` does not touch, so they are invariant rather than
merely checked.

What is refused is a statement that rebinds a constant, shadows one through the cref, or
**reopens a class the context already records** in a way that changes its ancestor chain, its
`new`, or its `initialize`. `Judge.casgn`'s `constAsgnOk` (§F18) already refused the first. -/
def ctxKept (κ κ' : Ctx) : Bool :=
  κ.consts.all (fun p => decide (envGet? κ'.consts p.1 = some p.2)) &&
  -- Inside a method body, no *new* constant key at all. That is not the restriction it looks
  -- like: `constGet?` resolves through the frame's cref, so a new qualified key can change the
  -- answer for a name whose binding did not move — and Ruby forbids the shape anyway
  -- ("dynamic constant assignment" is a SyntaxError inside a method).
  (match κ.frame with
   | none => true
   | some _ => κ'.consts.all (fun p => (envGet? κ.consts p.1).isSome)) &&
  κ.classes.all (fun c =>
    (ancestors? κ.classes c.name == ancestors? κ'.classes c.name) &&
    (!(smroGet? κ.classes c.name "new").isNone || (smroGet? κ'.classes c.name "new").isNone) &&
    (!(ctorGet? κ.classes c.name).isNone || (ctorGet? κ'.classes c.name).isNone)) &&
  (!mixinFreeChain κ.classes rootAncestors || mixinFreeChain κ'.classes rootAncestors)

/-! ## The judgment itself lived here, and is gone

`inductive Judge` and its seven companions — 83 rules, 1,750 lines — were deleted in clink 68
along with `chk`, its 177 hand derivations and its soundness proof. The replacement is
`Ratchet/Check.lean`'s `DJudge`: twelve rules, authored one at a time, each of which can only
join the certified judgment by acquiring an answer-typed semantic proof
(`Denote/Typed/`). `implementation-notes.md` clinks 65-68 and `AGENTS.md` record why 83 rules
with 48 value-shaped proofs could not be retrofitted into that discipline.

What survives in this file is the **datatype substrate** the semantic layer is indexed by:
`Ctx` and its three polarities, the class/method/constant tables and their accessors, and the
predicates `Denote/Sem/State.lean`'s conformance components read (`nameFreeN`, `clsGet?`,
`smroGet?`, `constGet?`, …). `StateOk κ Γ I m` needs a `κ`; this is where `κ` is defined.

Also surviving, and worth knowing they are here rather than being rediscovered: `PrimSig`,
`EqSafe`, `NilQSafe`, `Comparable`, `IterSig`, `NarrowCond` and the narrowing functions
(`narrowEnvs`/`narrowSpine`/`falsyTy`/`truthyTy`). Those are *tables and predicates*, not
rules, and each records a fact about CRuby that a `DPrim` row or a future narrowing rule will
want — `Ratchet/Check.lean`'s `DPrim` has 7 rows against `PrimSig`'s ~90 precisely so that the
obligation for each can be discharged one at a time. Nothing in the certified path reads them
today. -/



/-! ## The starting context

Moved here from `Ratchet/Validate.lean` when that file was deleted (clink 68): the *value*
is part of the context datatype's interface, and `Denote/Sem/State.lean`'s conformance
statements are the only consumers left. -/

/-- The starting context: no classes, no methods, no assumptions, no `self`. Every
emptiness is load-bearing, and for a different reason — the two syntax tables because
nothing is declared before a program's first statement, the assumption table because a
derivation carrying one is only a conditional claim, and `frame`/`selfTy` because a
program's top level is inside no method and runs somewhere `self` is not an instance of
anything this judgment models. The constant table is empty for the first of those reasons:
a program's first statement is the first thing that could assign one. -/
def ctx0 : Ctx := ⟨⟨[], [], [], [], true, []⟩, ⟨[], [], [], false, [], [], []⟩, ⟨none, [], none, none, [], true, none, true⟩⟩

end Ratchet
