import Denote.Sem.BuiltinsCapNumerics

/-!
# `Denote/Sem/BuiltinsCapObjects.lean` — `Builtins.runObjects`, for the heap half

The one dispatcher that needs the context-searching closers (`cap_arms_obj`): `Object#print` and
`Object#p` thread the machine through `printFold`/`pGo`, whose framing hypothesis has to be found
by `assumption`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

set_option maxHeartbeats 4000000 in
theorem runObjects_cap (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.runObjects bid recv args m = .ok v m' → MCap m m' := by
  intro v m' h
  rw [Builtins.runObjects.eq_def] at h
  dsimp only at h
  cap_arms_obj

#print axioms runObjects_cap

end Ratchet.Denote
