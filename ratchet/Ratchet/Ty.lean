import Ratchet.JsonUtil

/-!
The type language, **ported from `../lean/RubyCore/Types/Ty.lean`**: the constructors
and the pure helper functions (`arrowOf`/`arrowParts?`/`subTy`/`joinTy`/`mkNilable`,
`Env`/`envGet?`/`envSet`) are unchanged. **Not ported**: the metatheory around them
(`subTy_trans`, `joinTy_sub`, `SubEnv`/`subEnvB` and their soundness proofs, the
lambda-capture "pinning" machinery, `FrameCtx`) — none of it is needed by a checker with
no soundness theorem yet, and pulling it over would mean carrying proof debt this
package isn't using. If `Ratchet/Validate.lean` ever needs `subTy_trans` etc., port it
then, from the same source file.

Note what this type language does **not** have: no dedicated `str`/hash type. Strings
are `.cls "String"` — an instance of the class, same as every other object — and hashes
have no parameterised counterpart to `arrayOf` at all — the bare `.cls "Hash"` is all a
hash literal could be given, if `Ratchet/Validate.lean` had a rule for one yet (it does
not; see that file's scope note). Both are honest reflections of where the real project's
own type language currently stops, not gaps this port introduced.
-/

namespace Ratchet

open Lean (Json)

/-- The type language. No subtyping beyond `any`/`nilable` (`subTy` below): everything
else is compared by equality. -/
inductive Ty where
  | int
  | bool
  | nilT
  /-- A Symbol. -/
  | sym
  /-- An instance of the class named `name`. -/
  | cls (name : String)
  /-- The top type: some value, of a type the checker does not pin. Never inferred —
      only usable as a declared parameter type. -/
  | any
  /-- The class *object* named `name` (not an instance of it) — what `String` denotes
      as a receiver, distinct from `.cls "String"` (an instance of it). -/
  | clsOf (name : String)
  /-- `τ` or `nil`. -/
  | nilable (τ : Ty)
  | float
  /-- An `Array` whose elements are all `elem`. Invariant by design (compared by
      equality): covariance would be unsound under mutation-through-aliasing. -/
  | arrayOf (elem : Ty)
  /-- **A `Hash` whose keys are all `key` and whose values are all `val`** — `arrayOf` with two
      parameters, and added at tier 17b (clink 41) after being the widest-reaching gap this
      ladder had recorded (§Frontier item A: `Hash#fetch` is the slice's most-used builtin at 62
      sites, and `cvss.rb` cannot be typed at all without it).

      **Uniform, not keyed**, and that is the design decision. A per-key map would be more
      precise for a literal, and it is not what the target needs: `cvss.rb` reads its frozen
      tables as `TABLE.fetch(metric)` where `metric` is a *variable*, so no statically-known key
      is available and the useful fact is that every value in the table is a `Float`. A keyed
      type would answer nothing there while costing a third use of the binding spine.

      Invariant, for `arrayOf`'s reason and now with `arrayOf`'s precedent: tier 17a's
      `Array#<<` showed that invariance is what keeps `arrayOf .never`'s "provably empty"
      reading honest, and `hashOf .never .never` (the type of `{}`) inherits both the reading
      and the argument. -/
  | hashOf (key val : Ty)
  /-- **The bottom type: an expression that does not produce a value.** Added at tier 6
      (`../implementation-notes.md` clink 5), where the recursion in `fun-recursive-factorial`
      forced it, and it is *this* package's constructor — the ported
      `RubyCore/Types/Ty.lean` has no equivalent (see §Isolation).

      Three jobs, and it is worth being clear that they are the same job seen three ways:

      1. **The unit of `joinT`.** `joinT τ .never = τ`. If one branch of an `if` cannot
         return, the `if`'s value comes only from the other branch — so the join finally
         has an identity, and `elemTy` becomes an honest fold rather than a fold with a
         hand-written base case.
      2. **The type of a strict operand that never returns.** If evaluating a send's
         receiver or argument does not return, the send does not happen; its result type
         is vacuous. That is `Judge.primNever`/`Judge.callNever`.
      3. **The candidate a recursive call is given while its own signature is being
         found.** `Ratchet/Validate.lean`'s first pass over a function body types the
         recursive call at `.never` — "assume it does not come back" — which is what makes
         the *base* case of a recursion visible before the recursive case has a type. That
         first pass is a hint and is never trusted; see `Judge.callDef`.

      Like `.any` it is **inert**: no `PrimSig` row has it as a receiver and it is not
      `EqSafe`. Unlike `.any` it is inert from *below* — `.any` is "some value, type not
      pinned", `.never` is "no value at all" — and the two are not interchangeable
      anywhere: `arrayOf .never` is the precise type of `[]`, while `arrayOf .any` would be
      the type of an array whose elements are unknown. -/
  | never
  /-- A union: a value of `σ` or of `τ`. Binary, no normal form imposed. Inert on this
      package's checker path (nothing in `Ratchet/Validate.lean` constructs or narrows
      one yet) — a placeholder for the day two `if` branches of different class type
      need a real join instead of being rejected outright. -/
  | union (σ τ : Ty)
  /-- An arrow — the type of a value-level callable — spelled as a **params spine**:
      `(A, B) → R` is `arrowCons A (arrowCons B (arrow0 R))`. A spine, not
      `params : List Ty`, so `Ty` stays simple-recursive (a list payload would make it
      nested, and nested-derived equality doesn't kernel-reduce). -/
  | arrow0 (ret : Ty)
  | arrowCons (param : Ty) (rest : Ty)
  /-- **An instance of a user-defined class, carrying its instance variables' types.**
      Added at tier 7; this package's own constructor, not in the ported file.

      Why this rather than reusing `.cls name`: an object's observable type is not its class
      name. `Point.new(1, 2)` and `Point.new("a", "b")` are both `Point`s, and `getX`
      returns an `Integer` from one and a `String` from the other. Nothing about the class
      *declaration* decides that — Ruby writes no ivar types — so the only place the
      information exists is the instantiation, and the only way to keep it is to put it in
      the type. `.cls name` stays for the builtin classes (`String`, `Hash`), whose
      instances have no ivars this checker models.

      `ivars` is an **ivar spine** (`ivar0`/`ivarCons`), for exactly the reason `arrowOf` is
      a spine rather than a `List Ty`: a list payload would make `Ty` a nested inductive,
      and nested-derived `DecidableEq` does not kernel-reduce — which `Ratchet/Rungs.lean`'s
      per-rung `rfl` checks depend on. -/
  | inst (name : String) (ivars : Ty)
  /-- The empty ivar spine — an object with no instance variables set. -/
  | ivar0
  /-- One binding in a spine. For an ivar spine the name includes the `@` (the desugarer's
      own convention: `Expr.var .ivar "@x"`); tier 9 reuses the same two constructors for a
      closure's **captured locals**, where it does not. -/
  | ivarCons (name : String) (ty : Ty) (rest : Ty)
  /-- **A callable value: a reference to a block literal, plus the locals it captured.**
      Added at tier 9; this package's own constructor.

      Why not `arrowOf`, which has been in this `Ty` since the port and is still unused: an
      arrow needs its parameter types, and **Ruby writes none**. `f = lambda { |x| x + 1 }`
      says nothing about `x`; only `f.call(2)` does, and that is a different expression,
      possibly a different statement, possibly inside a different method. There is no
      principal type to infer without type variables, and this `Ty` has none.

      So a lambda's type is a *reference to its code*, and a call instantiates the body at
      the call site's argument types — the same move `Judge.callDef` makes for a named
      method, lifted to a value. `idx` indexes `Ctx.closures`, the table of every block
      literal in the program, collected once by `collectBlocks` before checking starts. It
      does not thread, so nothing here needs a fourth piece of state.

      `captured` is a binding spine (`ivar0`/`ivarCons`) holding the **locals as of the
      lambda's creation**, and it is in the type rather than in the table for a reason: two
      syntactically identical blocks share a table entry — harmless, since the entry is only
      `(params, body)` — but they need not have captured the same environment.
      `lambda-closure-capture` and `lambda-returns-lambda` are the two rungs that turn on
      this, the second because the inner lambda's captured `x` is the outer's *parameter*.

      **`selfTy` is the third field, added at tier 11.** A closure's body sees the `self` of
      wherever it was *created*, not of wherever it is called — so a lambda made inside a
      `Point` method and invoked inside a `Box` method must have its body checked against the
      `Point`. Tier 9 sidestepped that by *forbidding* creation anywhere but top level
      (`Judge.lambdaLit` carried a `κ.selfTy = none` premise, whose docstring named this field
      as the fix), and tier 11's cross-products are what brought it due: `xc-lambda-in-ivar`
      and `xc-module-applies-lambda` call a top-level lambda from inside a method, which the
      old restriction refused because it constrained the *call* site as well.

      Encoded as a `Ty` rather than an `Option Ty` because a `Ty` field must be one:
      **`.never` means "created where `self` was not typed"** (top level). `closSelf?` and
      `closSpine` decode it — the second because an `.inst n ivars` carries the creation
      object's instance variables, which is the spine the body must be judged against.

      Not `EqSafe`, and no `PrimSig` row has it as a receiver: the only rules that consume one
      are `Judge.closCall`'s `call`/`[]`. -/
  | clos (idx : Nat) (captured : Ty) (selfTy : Ty)
  /-- **"this local currently holds the same object as local `name`, and that object has type
      `τ`"** — an *alias*, added at tier 12 for `narrow-union-case-when`.

      Why a `Ty` and not a fourth threaded state. `case v when Integer` desugars to a
      temporary assigned from `v`, a test on the **temporary**, and branch bodies that use
      **`v`**:

      ```
      seq (vasgn local __dt_t1 (var local v))
          (if (send (const Integer) "===" [var local __dt_t1])
              (send (var local v) "*" [int 2])          -- v, not __dt_t1
              …)
      ```

      so narrowing has to reach a name the condition does not mention. Aliasing *is* state —
      created and destroyed by execution — and `implementation-notes.md` clink 17 argued that
      state a rule needs must **thread**, or its soundness becomes a list of places somebody
      has to remember. The environment already threads. Putting the alias in the environment's
      value type therefore gets the threading for free, and every place that could invalidate
      it is a place that already writes to the environment.

      **Nothing consumes a `sameAs` except `narrowEnvs`.** `Judge.var` *strips* it
      (`stripAlias`), so no expression ever has this type: it is a fact about a binding, not
      about a value, and it is inert in the same way `.any` is — no `PrimSig` row, not
      `EqSafe`, not `NilQSafe`, `isADispatchOk` refuses it.

      Three invalidations, and together they are exhaustive (see `Judge.vasgnAlias`):
      assignment to the alias's *holder* (which overwrites the binding), assignment to its
      *target* (`killAliasesTo`, in `Judge.vasgn`), and any call that could let a **block**
      reassign a captured local (`killAliases`, on those rules' outgoing environments). A
      branch that invalidates in one arm and not the other loses the alias at the join, because
      `joinT (sameAs y τ) τ` is a `union` and a `union` is not a `sameAs`. -/
  | sameAs (name : String) (τ : Ty)
deriving DecidableEq, BEq, Repr, Inhabited

/-- `(A, B, …) → R` from its parts. -/
def arrowOf : List Ty → Ty → Ty
  | [], r => .arrow0 r
  | p :: ps, r => .arrowCons p (arrowOf ps r)

/-- The inverse: a well-formed spine's parameter list and return type, `none` on
anything else. -/
def arrowParts? : Ty → Option (List Ty × Ty)
  | .arrow0 r => some ([], r)
  | .arrowCons p rest => (arrowParts? rest).map (fun (ps, r) => (p :: ps, r))
  | _ => none

/-- Subtyping: everything is below `any`; `nilable τ` also admits `nilT` and anything
below `τ`; otherwise compared by equality. -/
def subTy (σ τ : Ty) : Bool :=
  match σ, τ with
  | .never, _ => true
  | _, τ => match τ with
  | .any => true
  | .nilable τ' => σ == .nilT || σ == .nilable τ' || subTy σ τ'
  | _ => σ == τ

/-- Pointwise, at the arity the signature declares. A length mismatch is `false`. -/
def subTys : List Ty → List Ty → Bool
  | [], [] => true
  | σ :: σs, τ :: τs => subTy σ τ && subTys σs τs
  | _, _ => false

/-- `nilable` normalized at `nilT`: `nilable nilT` and `nilT` denote the same values. -/
def mkNilable (τ : Ty) : Ty := if τ == .nilT then .nilT else .nilable τ

/-- The join of two branch types (e.g. an `if`'s two branches): answers only the two
cases a small checker actually produces — equal types, or exactly one side `nil` — and
`none` otherwise (a real least-upper-bound over `union` is future work; see `Ty.union`'s
docstring). -/
def joinTy (σ τ : Ty) : Option Ty :=
  if σ == τ then some σ
  else if σ == .nilT then some (mkNilable τ)
  else if τ == .nilT then some (mkNilable σ)
  else if σ == .nilable τ then some σ
  else if τ == .nilable σ then some τ
  else none

/-- Local-variable typing environment. `envSet` replaces in place, matching the source
file's own "order is canonical" convention (not load-bearing here — this package
compares types, not whole environments). -/
abbrev Env := List (String × Ty)

def envGet? (Γ : Env) (x : String) : Option Ty :=
  (Γ.find? (·.1 == x)).map (·.2)

/-! ### Aliases (tier 12)

`Ty.sameAs`'s docstring has the design; these are its four operations. Every one of them is
the **identity** on an alias-free environment, which is what let the alias be threaded through
the existing rules without editing a single derivation term already on file. -/

/-- Is this binding an alias? `Judge.var`'s guard -- see `Judge.varAlias` for why the split is
a rule and not a `stripAlias` in the conclusion. -/
def isAliasTy : Ty → Bool
  | .sameAs _ _ => true
  | _ => false

/-- The type behind an alias — what a *read* of the name produces. `Judge.var` applies this, so
no expression ever has type `sameAs`. -/
def stripAlias : Ty → Ty
  | .sameAs _ τ => τ
  | τ => τ

/-- Drop every alias in an environment, keeping the underlying types.

Applied where a **block** could have reassigned a captured local without the checker seeing the
assignment: those rules carry the caller's environment out unchanged (justified by `capIntact`,
which compares *types*), and a value can change at a fixed type. So the type survives and the
alias must not. -/
def killAliases : Env → Env
  | [] => []
  | (x, τ) :: Γ => (x, stripAlias τ) :: killAliases Γ

/-- Drop only the aliases *pointing at* `x`. `Judge.vasgn` applies this before binding `x`: once
`x` holds a new object, nothing else holds the same one. -/
def killAliasesTo : Env → String → Env
  | [], _ => []
  | (y, τ) :: Γ, x =>
    (y, match τ with
        | .sameAs n ρ => if n == x then ρ else .sameAs n ρ
        | _ => τ) :: killAliasesTo Γ x

def envSet : Env → String → Ty → Env
  | [], x, τ => [(x, τ)]
  | (y, σ) :: Γ, x, τ => if y == x then (x, τ) :: Γ else (y, σ) :: envSet Γ x τ

partial def Ty.ofJson? (j : Json) : Except String Ty := do
  let tag ← j.getObjValAs? String "tag"
  match tag with
  | "int" => return .int
  | "bool" => return .bool
  | "nilT" => return .nilT
  | "sym" => return .sym
  | "cls" => return .cls (← j.getObjValAs? String "name")
  | "any" => return .any
  | "clsOf" => return .clsOf (← j.getObjValAs? String "name")
  | "nilable" => return .nilable (← Ty.ofJson? (← j.getObjVal? "elem"))
  | "float" => return .float
  | "arrayOf" => return .arrayOf (← Ty.ofJson? (← j.getObjVal? "elem"))
  | "union" =>
    let l ← Ty.ofJson? (← j.getObjVal? "l")
    let r ← Ty.ofJson? (← j.getObjVal? "r")
    return .union l r
  | "arrow0" => return .arrow0 (← Ty.ofJson? (← j.getObjVal? "ret"))
  | "arrowCons" =>
    let param ← Ty.ofJson? (← j.getObjVal? "param")
    let rest ← Ty.ofJson? (← j.getObjVal? "rest")
    return .arrowCons param rest
  | other => throw s!"Ty.ofJson?: unknown tag '{other}'"

/-! ## Ratchet-local additions (a deliberate fork of the ported file)

Everything above is `RubyCore/Types/Ty.lean` verbatim. Everything below is **new here**,
added when tier 4 (`if`) forced it, and is therefore a place this package's copy and the
real model's have deliberately diverged — see `AGENTS.md` §Isolation on what to do about
that. The reason it could not be a use of the ported `joinTy`: that function answers
`none` for two unrelated branch types, and an `if` rule that fails there is not merely
imprecise, it cannot type `if c then 1 else "a"` at all. `Ty.union` was already in the
grammar and inert; these functions are what put it to work. -/

/-- The members of a (possibly nested) union, flattened left to right. A non-union is a
one-member union of itself. -/
def unionMems : Ty → List Ty
  | .union σ τ => unionMems σ ++ unionMems τ
  | τ => [τ]

/-- Rebuild a right-nested union from a member list. `[]` cannot arise from `unionMems`
(it always yields at least one member), and is mapped to `.nilT` rather than making this
function partial. -/
def unionOf : List Ty → Ty
  | [] => .nilT
  | [τ] => τ
  | τ :: τs => .union τ (unionOf τs)

/-- Order-preserving duplicate removal. Accumulator-passing so the recursion is
structural on the input list. -/
def dedupTysAux (seen : List Ty) : List Ty → List Ty
  | [] => seen.reverse
  | τ :: τs => if seen.contains τ then dedupTysAux seen τs else dedupTysAux (τ :: seen) τs

def dedupTys (τs : List Ty) : List Ty := dedupTysAux [] τs

/-- **The total join.** Tries the ported `joinTy`'s structural cases first (equal types,
one side `nil`, one side the other's `nilable`) so the common shapes keep their familiar
answers, and otherwise builds a **normalized union** of both sides' members.

Normalization is not cosmetic: `elsif-chain-mismatch` desugars to nested `if'`s, so the
outer join sees `Int` against `union(Int, String)`. Flatten-and-dedup gives
`union(Int, String)`; without it the answer would be `union(Int, union(Int, String))`,
which denotes the same values but is a different `Ty`, and `Ty` is compared by equality
everywhere in this package.

What a union *means* here — worth being explicit, because tier 4 is where the type
language shifts register: a `Ty` is an **upper bound** on the values an expression can
produce, not an exact description. Nothing consumes a union (no `PrimSig` row has one as
a receiver, and it is not `EqSafe`), so producing one is always safe: it says "this
checker knows the value is one of these", and any rule that wants to *use* the value
will simply fail to apply. -/
def joinT (σ τ : Ty) : Ty :=
  if σ == .never then τ
  else if τ == .never then σ
  else match joinTy σ τ with
  | some ρ => ρ
  | none => unionOf (dedupTys (unionMems σ ++ unionMems τ))

/-! ## Ivar spines

An object's instance-variable state is a `Ty` (a spine), not an `Env`, so that it can sit
inside `Ty.inst`. These two functions are the spine's `envGet?`/`envSet`, and the
difference from `Env`'s pair is the whole content of `class-ivar-lazy-nil`. -/

/-- An ivar's type, or `none` if the object has never been given one.

Callers must decide what `none` means, and the judgment's answer is `.nilT`: in Ruby,
reading an instance variable that was never assigned yields `nil` — it does not raise, and
it does not even warn under `-w` for a *read* in a method. That is `class-ivar-lazy-nil`
(`class Box; def reveal; @secret; end; end; Box.new.reveal` is `nil`), and it is why the
lookup is separated from the defaulting. -/
def ivarGet? : Ty → String → Option Ty
  | .ivarCons n τ rest, x => if n == x then some τ else ivarGet? rest x
  | _, _ => none

/-- Record an ivar's type, replacing in place, appending at the end otherwise.

The last case — a `Ty` that is not a spine at all — returns it unchanged rather than
failing. That case is unreachable from the judgment, which only ever builds spines starting
from `.ivar0`, and making the function total is cheaper than threading an `Option` through
every assignment rule. -/
def ivarSet : Ty → String → Ty → Ty
  | .ivar0, x, ρ => .ivarCons x ρ .ivar0
  | .ivarCons n τ rest, x, ρ =>
    if n == x then .ivarCons x ρ rest else .ivarCons n τ (ivarSet rest x ρ)
  | other, _, _ => other

/-! ## Joining spines (tier 12)

`joinEnv` for the ivar spine. Added when `narrow-union-in-ivar` forced it: `Judge.if'` used to
*require* the two branches to agree on the spine (`I₁ = I₂`, clink 6), which made
`if flag then @v = 1 else @v = "s" end` untypeable — and so made an object whose ivar type
depends on a constructor argument not describable at all.

Clink 6's argument for requiring agreement was that a spine is part of the *type* of `self`
(see `Ty.inst`) and there is no widening of it that keeps that type honest. Narrowing is what
makes the widening honest: `@v : union Int String` is now a type something can *consume*, so
the union is a real upper bound rather than a dead end.

Same defaulting as `joinEnv`, for the same reason one level down: a name bound in only one
branch joins against `.nilT`, because reading an instance variable that was never assigned
yields `nil` (`ivarGet?`'s docstring, and `class-ivar-lazy-nil`). -/

/-- The names bound in a spine, in order. -/
def spineKeys : Ty → List String
  | .ivarCons x _ rest => x :: spineKeys rest
  | _ => []

def joinSpineAt (I₁ I₂ : Ty) : List String → Ty
  | [] => .ivar0
  | x :: xs =>
    .ivarCons x (joinT ((ivarGet? I₁ x).getD .nilT) ((ivarGet? I₂ x).getD .nilT))
      (joinSpineAt I₁ I₂ xs)

/-- The join of two branch **spines**, pointwise over the union of their names.

Note `joinSpine I I = I` for any spine `I`, and *definitionally* so — `joinT τ τ` reduces to
`τ` and the key order is `I`'s own. That is not a nicety: it is what let `Judge.if'`'s spine
premise be generalized from `I₁ = I₂` to `joinSpine I₁ I₂ = I₃` **without editing a single one
of the derivation terms already on file**, each of which discharges it with the same `rfl`. -/
def joinSpine (I₁ I₂ : Ty) : Ty :=
  joinSpineAt I₁ I₂ (spineKeys I₁ ++ (spineKeys I₂).filter (fun k => !(spineKeys I₁).contains k))

/-! ## Locals as a spine

Tier 9 needs a local environment inside a `Ty` (a closure's captured bindings — see
`Ty.clos`), which is the same shape problem the ivars had, so it is the same solution. These
two convert; `spineToEnv` on a non-spine answers `[]`, which is unreachable from the judgment
and cheaper than threading an `Option`. -/

/-- A closure's captured environment, as a spine. **Aliases are stripped** (tier 12): a
`sameAs` is a fact about one environment, and a captured spine is copied into a `Ty` that
travels — so carrying it would let a block body's `narrowEnvs` refine a name that means
something else there (a parameter shadowing the target, say). Stripping is also what keeps
`capIntact`'s two sides comparable. -/
def envToSpine : Env → Ty
  | [] => .ivar0
  | (x, τ) :: Γ => .ivarCons x (stripAlias τ) (envToSpine Γ)

def spineToEnv : Ty → Env
  | .ivarCons x τ rest => (x, τ) :: spineToEnv rest
  | _ => []

/-! ### Stale closure captures (clink 46)

**A captured spine is a claim about a binding, not about a value** — the same thing
`Ty.sameAs` is, and it goes stale the same way. A Ruby block captures locals *by reference*,
so `f = lambda { x }` records `x`'s type into `f`'s `Ty.clos` spine and a later `x = "a"`
makes that record wrong. Without the two functions below, `Judge.vasgn` certified

```ruby
x = 1
f = lambda { x }
x = "a"
f.call + 1        -- CRuby: TypeError
```

as `Integer` (`found-issues.md` §F1 — a `validate` `true` on a **type-stuck** program, found
by the semantic ratchet reading `Obl.Judge.vasgn`, not by any corpus rung).

The fix is `killAliasesTo`'s, one level up: an assignment invalidates the facts other
bindings recorded about the assigned name. Three things about the shape are deliberate.

* **It is precise, not blanket.** A capture only goes stale if the recorded type *differs*
  from the new one; `x = 1; f = lambda { x }; x = 2` keeps `f`'s spine, because
  `x : Integer` is still true. That is the same boundary `capIntact` draws for a block body
  that assigns to a captured local, and it is what keeps the common case typable.
* **It erases to `.any`, not to nothing.** Dropping the binding would make a later *read* of
  `f` underivable (`Judge.var` needs `envGet?` to answer), which is a worse error message for
  the same rejection. `.any` keeps the name bound, and is unusable on purpose: it matches no
  `PrimSig` row, is not `EqSafe`, and is not a `.clos`, so `f.call` has no rule.
* **It walks the whole type.** A stale capture can sit under a `nilable`, inside an array
  element, in an `inst`'s ivar spine, or in another closure's captured spine
  (`g = lambda { x }; f = lambda { g }`), and any of those makes the *whole* binding
  unsound to keep. Erasing the outermost type is sound because every value inhabits `.any`.

Both are the **identity on a closure-free environment**, which is what let them be added to
two rules already carrying 177 derivations without editing one of them — exactly the property
`killAliases`' docstring claims for the alias operations. -/

/-- Does `σ` record a closure capture of `x` at a type other than `τ`?

The `.clos` arm reads the captured spine's own entry for `x` (`ivarGet? cap x`, since a
capture spine is keyed by local name) and *also* recurses into the spine, because an entry may
itself be a closure over `x`. -/
def capStale (x : String) (τ : Ty) : Ty → Bool
  | .clos _ cap selfT =>
      (match ivarGet? cap x with
       | some σ => σ != τ
       | none => false)
        || capStale x τ cap || capStale x τ selfT
  | .nilable ρ => capStale x τ ρ
  | .arrayOf ρ => capStale x τ ρ
  | .hashOf k v => capStale x τ k || capStale x τ v
  | .union a b => capStale x τ a || capStale x τ b
  | .sameAs _ ρ => capStale x τ ρ
  | .inst _ I => capStale x τ I
  | .ivarCons _ σ rest => capStale x τ σ || capStale x τ rest
  | .arrow0 r => capStale x τ r
  | .arrowCons p rest => capStale x τ p || capStale x τ rest
  | _ => false

/-- Widen every binding whose type records a stale capture of `x` to `.any`. Applied by
`Judge.vasgn`/`Judge.vasgnAlias` beside `killAliasesTo`. -/
def killClosOver : Env → String → Ty → Env
  | [], _, _ => []
  | (y, σ) :: Γ, x, τ =>
    (y, if capStale x τ σ then .any else σ) :: killClosOver Γ x τ

/-- The same, over an **ivar spine**. `@f = lambda { x }` puts a `Ty.clos` in `self`'s spine,
which `Judge.vasgn` threads out untouched; the spine goes stale for the same reason the
environment does, so it gets the same treatment. -/
def killClosOverSpine : Ty → String → Ty → Ty
  | .ivarCons n σ rest, x, τ =>
    .ivarCons n (if capStale x τ σ then .any else σ) (killClosOverSpine rest x τ)
  | other, _, _ => other

/-- The names bound in an environment, in order. -/
def envKeys : Env → List String
  | [] => []
  | (k, _) :: Γ => k :: envKeys Γ

/-- Pointwise environment join at a given list of names. -/
def joinEnvAt (Γ₁ Γ₂ : Env) : List String → Env
  | [] => []
  | k :: ks =>
    (k, joinT ((envGet? Γ₁ k).getD .nilT) ((envGet? Γ₂ k).getD .nilT))
      :: joinEnvAt Γ₁ Γ₂ ks

/-- The join of two branch **environments**, pointwise over the union of their names.

A name bound in only one branch joins against `.nilT`, because that is what Ruby does:
the parser declares a local at the assignment's *syntactic* position, so
`if false then y = 1 end; y` evaluates to `nil` rather than raising.

Unlike `joinT`, this exists for a **soundness** reason, not a precision one — see
`corpus/042-if-does-not-leak-reassignment`, a program that really raises `TypeError` and
that a checker carrying the pre-`if` environment forward would certify. -/
def joinEnv (Γ₁ Γ₂ : Env) : Env :=
  joinEnvAt Γ₁ Γ₂ (envKeys Γ₁ ++ (envKeys Γ₂).filter (fun k => !(envKeys Γ₁).contains k))

/-! ## Narrowing: the four refinements

Tier 12. `nilable` and `union` are the two types this package can *produce* but has no way
to *consume* — no `PrimSig` row takes either as a receiver, and neither is `EqSafe`. These
four functions are what makes consuming one possible: given that a runtime test on a value
of type `τ` went one way, they say what is left.

Each is a claim about **Ruby's truth values**, and the one that carries all the weight is
this: *in Ruby, the only falsy values are `nil` and `false`.* Not `0`, not `""`, not `[]`.
So for every type in this language except `nilT`, `bool`, `nilable _`, `union _ _` and
`any`, every value of that type is truthy — which is why `falsyTy` answers `.never` (the
branch does not run) on all of them, and why that answer is *precise* rather than reckless.

`.any` refines to `.any` throughout: the checker does not know what the value is, so it
learns nothing from the test. `.bool` refines to `.bool` in both directions, because `Ty`
has no singleton `true`/`false` types — a place the refinement is deliberately imprecise,
and harmlessly so (`.bool`'s only `PrimSig` row is `!`).

Note what is *not* here: these functions never look at the ivar spine of an `.inst`, and
never manufacture a type the grammar did not already have. Narrowing is a projection out
of a union, not a computation of a new type. -/

/-- The values of `τ` that are **truthy** — everything except `nil` and `false`. Used for
the then-branch of `if x` and the else-branch of `if x.nil?`. -/
def truthyTy : Ty → Ty
  | .nilT => .never
  | .bool => .bool
  | .any => .any
  | .nilable ρ => truthyTy ρ
  | .union σ τ => joinT (truthyTy σ) (truthyTy τ)
  | τ => τ

/-- The values of `τ` that are **falsy** — `nil` and `false`, and nothing else. Used for
the else-branch of `if x`.

The `_ => .never` case is the whole point: `if x` where `x : Int` has an else-branch that
cannot run, so the branch is typed with `x : never` and anything it computes is vacuous.
That is only sound because Ruby's falsiness is exactly `{nil, false}`. -/
def falsyTy : Ty → Ty
  | .nilT => .nilT
  | .bool => .bool
  | .any => .any
  | .nilable ρ => joinT .nilT (falsyTy ρ)
  | .union σ τ => joinT (falsyTy σ) (falsyTy τ)
  | _ => .never

/-- The values of `τ` that are `nil`. Used for the then-branch of `if x.nil?`. Unlike
`falsyTy`, `false` is *not* included: `false.nil?` is `false`. -/
def isNilTy : Ty → Ty
  | .nilT => .nilT
  | .any => .any
  | .nilable _ => .nilT
  | .union σ τ => joinT (isNilTy σ) (isNilTy τ)
  | _ => .never

/-- The values of `τ` that are not `nil`. Used for the else-branch of `if x.nil?`. Differs
from `truthyTy` at `.bool` only in intent — both answer `.bool` — and at
`nilable bool`, where this one keeps the `bool` that `truthyTy` also keeps. The two are
genuinely different functions at `union(nilT, bool)`-shaped types, and separating them is
cheaper than arguing they coincide. -/
def nonNilTy : Ty → Ty
  | .nilT => .never
  | .any => .any
  | .nilable ρ => nonNilTy ρ
  | .union σ τ => joinT (nonNilTy σ) (nonNilTy τ)
  | τ => τ

/-- The element type of an array literal, from its elements' types: the `joinT` of all
of them.

`Ty.arrayOf` takes **one** element type and Ruby arrays are heterogeneous, so this is
where tier 4's join earns its keep a second time: `[1, "a", true]` is ordinary safe Ruby,
and its type is `arrayOf (union Int (union String Bool))` — a genuine upper bound on every
element, which is exactly what `arrayOf τ` claims.

**The empty case is `.never`, and it now really is the join's unit.** `[] : arrayOf never`
reads "every element of this array does not return a value", which is vacuously true of an
array with no elements and is the *most precise* such claim. Tier 5 wrote `.any` here
because `Ty` had no bottom type and the fold needed a hand-written singleton base case to
avoid widening `[1]` to `arrayOf any` by passing through the unit; tier 6's `Ty.never`
removed the need for both (clink 5). -/
def elemTy : List Ty → Ty
  | [] => .never
  | τ :: τs => joinT τ (elemTy τs)

end Ratchet
