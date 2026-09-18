import Ratchet.Lang.Expr
import Ratchet.Lang.Ty

/-!
# `Ratchet/Static/Predicates.lean`

The **static predicates**: which receiver types make a method total, which names are
`Object`'s, which are builtin or exception classes, and the sixteen primitive signature
rows. Relations over types and names only — no table, no context, no expression.
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

end Ratchet
