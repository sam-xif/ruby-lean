import Denote.Sem.BuiltinsCapCollections

/-!
# `Denote/Sem/BuiltinsCapStrings.lean` — `Builtins.runStrings`, for the heap half

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
theorem runStrings_cap (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.runStrings bid recv args m = .ok v m' → MCap m m' := by
  intro v m' h
  rw [Builtins.runStrings.eq_def] at h
  dsimp only at h
  cap_arms_rx
  -- **Three arms closed by hand**, the same way `FrameLocal.lean` hand-writes `newImpl_locals`:
  -- automation that is cheap enough for six hundred arms will not be complete on all of them,
  -- and widening the shared closer list to reach these three slows every other dispatcher.
  -- `String#[]` with a `Regexp` selector delegates to `runRegex`; `Symbol#to_proc` allocates the
  -- layer's one Proc; and `String#freeze` on a `dup` is the push-a-copy-then-set composite.
  all_goals (obtain ⟨-, rfl⟩ := h)
  all_goals (first
    | exact ((allocMData_cap _ _ _ _ _).trans (setMatchGlobals_cap _ _)).trans
        (runRegex_cap _ _ _ _ _ _ (by assumption))
    | exact MCap.push_copy_then_set rfl rfl rfl
    | (refine MCap.push_eq rfl ?_; cap_free)
    | cap_close
    | (cap_norm; cap_close))

#print axioms runStrings_cap



end Ratchet.Denote
