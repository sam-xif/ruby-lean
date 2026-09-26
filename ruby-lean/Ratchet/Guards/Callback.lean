import Ratchet.Guards.ClosureFlow

/-! An ordinary method receiving a checked callback keeps its actual method frame and
exact block code. This type records identity; the callback body proof supplies safety. -/
namespace Ratchet

def callbackMethodCtx (κ : Ctx) (fr : Frame) (code : ClosureCode) : Ctx :=
  (κ.withoutRuntimeScope.withFrame (some fr)).withBlockTy (some (.clos code .ivar0 .never))

end Ratchet
