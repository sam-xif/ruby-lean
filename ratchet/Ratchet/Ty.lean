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
