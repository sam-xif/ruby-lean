import Ratchet.Static.Capture

/-!
# `Ratchet/Static/Narrow.lean`

Tier 12's **narrowing**: the refinements (`isATy`/`notATy`/`refineThen`/`refineElse`), the
conditions that license them (`NarrowCond`, and the guards that keep a narrowed name honest),
and the two environments/spines a conditional's branches are judged in.
-/

namespace Ratchet

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

end Ratchet
