import Ratchet.Expr
import Ratchet.Ty

/-!
# `Judge` — the hand-authored typing judgment

The **specification** half of the checker. `Ratchet/Validate.lean`'s `chk` is a
decision procedure; this file says *what it is deciding*. The split matters for the
ratchet: a rung is only honestly "climbed" when there is a derivation `Judge p τ`
one can read and check by eye, not merely a `Bool` that came out `true`.

## Scope: exactly the first 13 rungs, and no more

Deliberately authored for rungs 1–13 of `corpus/` (tier 1's eight literals, plus
`add`/`sub`/`mul`/`div`/`str-concat`), and nothing else. Consequences, each a real
limitation to lift later, not an oversight:

- **No environment.** `Judge` relates a *closed* `Expr` to a `Ty`; there is no `Env`
  parameter because no rung below 14 mentions a variable. Tier 3 (`var`/`vasgn`/`seq`)
  is where `Judge` grows a `Γ`, and that is a change to every rule's shape, so it is
  better done when a rung forces it than guessed at now.
- **No `subTy` anywhere.** Every rule below matches types by construction. `subTy`
  exists in `Ratchet/Ty.lean` and is unused here on purpose: with no parameters and no
  `any`, there is nothing yet for subsumption to do, and a subsumption rule admitted
  "for later" is a rule whose soundness nobody has had to justify against a rung.
- **No `if`/join, no `def`, no dispatch.** Tiers 4–9.

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

mutual

/-- `Judge e τ`: the closed expression `e` has type `τ`. No certificate parameter —
nothing here is trusted; see the module docstring.

Read each literal rule as an assertion about the real semantics: evaluating this literal
yields a value whose class is the one `τ` names. `Check13.lean` checks precisely that,
by running the actual `stepFn`. -/
inductive Judge : Expr → Ty → Prop
  /-- An integer literal — including a negative one: `-5` desugars to `int (-5)`, not to
      a unary send (rung 008), so this single rule covers both. -/
  | intLit {n : Int} : Judge (.int n) .int
  /-- A float literal. `Expr.flt` carries IEEE bits; the type does not depend on them,
      so no side condition. -/
  | fltLit {bits : UInt64} : Judge (.flt bits) .float
  /-- A string literal is *an instance of* `String` — `.cls "String"`, never a
      dedicated `str` type; this type language has none (`Ratchet/Ty.lean`). -/
  | strLit {s : String} : Judge (.str s) (.cls "String")
  | symLit {s : String} : Judge (.sym s) .sym
  /-- `true` and `false` share one type. `Ty` has no singleton-`true` type, and Ruby's
      two distinct classes (`TrueClass`/`FalseClass`) are not distinguished here —
      `Ty.bool` covers both, which is why rungs 002 and 003 both target `.bool`. -/
  | truLit : Judge .tru .bool
  | flsLit : Judge .fls .bool
  /-- `nil : Nil` — the singleton type, not `nilable` of anything. -/
  | nilLit : Judge .nil .nilT
  /-- An explicit-receiver, block-less `send` whose receiver and arguments type, and
      whose resulting shape has a justified `PrimSig`.

      Three restrictions are each doing work: `some recv` (an implicit-self send has
      nobody to dispatch on in this fragment), `blk = none` (a block would need
      `Expr.block` typing, tier ≥ 6), and `PrimSig` matching the *synthesized* argument
      types exactly (no subsumption — see the module docstring). -/
  | prim {recv : Expr} {m : String} {args : List Expr}
      {σ τ : Ty} {argTys : List Ty} :
      Judge recv σ → JudgeAll args argTys → PrimSig σ m argTys τ →
      Judge (.send (some recv) m args none) τ

/-- Pointwise `Judge` over an argument list, with matching length by construction. -/
inductive JudgeAll : List Expr → List Ty → Prop
  | nil : JudgeAll [] []
  | cons {e : Expr} {es : List Expr} {τ : Ty} {τs : List Ty} :
      Judge e τ → JudgeAll es τs → JudgeAll (e :: es) (τ :: τs)

end

end Ratchet
