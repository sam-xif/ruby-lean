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
have no parameterised counterpart to `arrayOf` at all (`Ratchet/Validate.lean` types a
hash literal as the bare `.cls "Hash"`, unparameterised). Both are honest reflections of
where the real project's own type language currently stops, not gaps this port
introduced.
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
  match τ with
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

end Ratchet
