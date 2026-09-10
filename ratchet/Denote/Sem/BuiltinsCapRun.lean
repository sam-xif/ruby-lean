import Denote.Sem.BuiltinsCapObjects

/-!
# `Denote/Sem/BuiltinsCapRun.lean` — `Builtins.run`, and **`BuiltinsSeal` proved**

The top of the dispatcher chain, and the conclusion of the layer `HANDOFF.md` names as the
resume point: the frame half is `Denote/Sem/FrameLocal.lean`'s 600-arm `builtins_run_locals`,
the heap half is `builtins_run_cap` below, and `Sealed.of_capMono` is the join.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

set_option maxHeartbeats 4000000 in
theorem builtins_run_cap (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.run bid recv args m = .ok v m' → MCap m m' := by
  intro v m' h
  rw [Builtins.run.eq_def] at h
  dsimp only at h
  cap_arms_obj

#print axioms builtins_run_cap

/-! ## `BuiltinsSeal`, proved

`Denote/Sem/StepLocal.lean` left this stated and unproved on the grounds that "one builtin
measured is not the layer walked". The layer is now walked. -/

theorem builtinsSeal : BuiltinsSeal := fun _b bid recv args m hs _ _ v m' hrun =>
  hs.of_capMono (builtins_run_locals bid recv args m v m' hrun)
    (builtins_run_cap bid recv args m v m' hrun)

#print axioms builtinsSeal

/-- …and the bookkeeping half, which `Sealed.push` needs beside it. -/
theorem builtinsFramesWF {bid : String} {recv : Value} {args : List Value} {m : Machine}
    {v : Value} {m' : Machine} (hrun : Builtins.run bid recv args m = .ok v m')
    (h : FramesWF m) : FramesWF m' :=
  h.of_capMono (builtins_run_locals bid recv args m v m' hrun)
    (builtins_run_cap bid recv args m v m' hrun)

#print axioms builtinsFramesWF

end Ratchet.Denote
