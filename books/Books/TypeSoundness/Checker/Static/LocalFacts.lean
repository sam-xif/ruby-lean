import Books.TypeSoundness.Checker.Lang.Ty

/-! Flow facts distinct from local value types. Exact slots include bound nil values;
current Procs capture this activation and have no singleton dispatch class. These facts
must be updated by effects, not inferred from Ty.clos or copied across body entry. -/
namespace Checker

structure LocalFacts where
  slots : Option (List String) := none
  currentProcs : List String := []
  /-- Known present slots, even when the entire physical domain is unknown. -/
  bound : List String := []
deriving BEq, DecidableEq, Repr, Inhabited

namespace LocalFacts

def empty : LocalFacts := ⟨some [], [], []⟩

/-- Assignment creates a slot in an uncaptured frame and replaces only the target's
origin fact. Other aliases still point to the same closure after this binding changes. -/
def write (f : LocalFacts) (x : String) (current : Bool) : LocalFacts :=
  ⟨f.slots.map (x :: ·),
    (if current then [x] else []) ++ f.currentProcs.filter (· != x), x :: f.bound⟩

def copy (f : LocalFacts) (x y : String) : LocalFacts :=
  f.write x (f.currentProcs.contains y)

/-- Unknown effects discard origin and slot claims; they do not invent absence. -/
def unknown : LocalFacts := ⟨none, [], []⟩

/-- Certified effects may add slots and overwrite values, but cannot remove an
already bound caller slot. Preserve presence without claiming origins or absence. -/
def afterEffect (f : LocalFacts) : LocalFacts := ⟨none, [], f.bound⟩

/-- Classify only names typed at body return. Known-present slots suffice if they
cover those names; otherwise an exact domain is needed to separate fresh body locals. -/
def captureNames? (f : LocalFacts) (Γ : Env) : Option (List String) :=
  match f.slots with
  | some names => some names
  | none => if Γ.all (fun p => f.bound.contains p.1) then some f.bound else none

end LocalFacts

def captureEnv (names : List String) : Env → Env
  | [] => []
  | (x, τ) :: Γ => if names.contains x then (x, deAlias τ) :: captureEnv names Γ else captureEnv names Γ

/-- Discard all bindings hidden by parameter/block-local names, including duplicates. -/
def withoutNames (names : List String) : Env → Env
  | [] => []
  | (x, τ) :: Γ => if names.contains x then withoutNames names Γ else (x, τ) :: withoutNames names Γ

/-- Shadowed names recover caller types; other names use the body's outgoing capture
types. Alias identities are erased on both sides of the frame boundary. -/
def closureReturnEnv (shadow names : List String) (caller body : Env) : Env :=
  captureEnv shadow caller ++ captureEnv names (withoutNames shadow body)

end Checker
