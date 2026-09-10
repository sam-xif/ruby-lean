import Denote.Sem.BuiltinsCapStrings

/-!
# `Denote/Sem/BuiltinsCapNumerics.lean` — `Builtins.runNumerics`, for the heap half

The dispatcher that forced the `simp at h` demotion: with `simp` reachable early, this arm set
took the elaborator to **14 GB of proof term without terminating**, because on an arithmetic arm
`simp` tries to *evaluate* the `Int`/`Float` literals. `dsimp only at h` does the one thing that
was actually needed — beta-reducing a `(fun b => match …) b` arm so `split` can see the match —
definitionally, and this file then closes in seconds.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

set_option maxHeartbeats 4000000 in
theorem runNumerics_cap (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.runNumerics bid recv args m = .ok v m' → MCap m m' := by
  intro v m' h
  rw [Builtins.runNumerics.eq_def] at h
  dsimp only at h
  cap_arms

#print axioms runNumerics_cap

end Ratchet.Denote
