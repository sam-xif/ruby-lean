import Books.TypeSoundness.Checker.Guards.ClosureFlow

/-! An ordinary method receiving a checked callback keeps its actual method frame and
exact block code. Actual receiver identity is a separate fact; the callback body proof
supplies safety. -/
namespace Checker

def callbackMethodCtx (κ : Ctx) (fr : Frame) (code : ClosureCode) : Ctx :=
  (κ.withoutRuntimeScope.withFrame (some fr)).withBlockTy (some (.clos code .ivar0 .never))

end Checker
