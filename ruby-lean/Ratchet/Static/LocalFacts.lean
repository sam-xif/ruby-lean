import Ratchet.Lang.Ty

/-! Flow facts distinct from local value types. Exact slots include bound nil values;
current Procs capture this activation and have no singleton dispatch class. These facts
must be updated by effects, not inferred from Ty.clos or copied across body entry. -/
namespace Ratchet

structure LocalFacts where
  slots : Option (List String) := none
  currentProcs : List String := []
deriving BEq, DecidableEq, Repr, Inhabited

namespace LocalFacts

def empty : LocalFacts := ⟨some [], []⟩

/-- Assignment creates a slot in an uncaptured frame and replaces only the target's
origin fact. Other aliases still point to the same closure after this binding changes. -/
def write (f : LocalFacts) (x : String) (current : Bool) : LocalFacts :=
  ⟨f.slots.map (x :: ·),
    (if current then [x] else []) ++ f.currentProcs.filter (· != x)⟩

def copy (f : LocalFacts) (x y : String) : LocalFacts :=
  f.write x (f.currentProcs.contains y)

/-- Unknown effects discard origin and slot claims; they do not invent absence. -/
def unknown : LocalFacts := ⟨none, []⟩

end LocalFacts
end Ratchet
