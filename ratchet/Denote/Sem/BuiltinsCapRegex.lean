import Denote.Sem.BuiltinsCap

/-!
# `Denote/Sem/BuiltinsCapRegex.lean` — `Builtins.runRegex`, for the heap half

One dispatcher per module, and that is a **measurement decision** rather than tidiness: Lean
buffers a module's messages until the module ends, so a single file holding all six is a black
box for as long as it runs, and a failure in the last one discards the first five. Split, `lake`
prints a line per dispatcher and caches each success. `RubyCore/Proof/KontFrameDispatch.lean`
made the same split for the same reason.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

set_option maxHeartbeats 40000000 in
set_option profiler true in
set_option profiler.threshold 400 in
theorem runRegex_cap (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.runRegex bid recv args m = .ok v m' → MCap m m' := by
  intro v m' h
  rw [Builtins.runRegex.eq_def] at h
  dsimp only at h
  cap_arms_rx

#print axioms runRegex_cap

end Ratchet.Denote
