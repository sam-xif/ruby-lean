import Ratchet.Judge

/-! Enter the lexical scope of a fresh class, without advertising future methods. -/
namespace Ratchet

def classBodyCtx (κ : Ctx) (name : String) : Ctx :=
  { κ with
    scope := { κ.scope with
      frame := none
      blockTy := none
      selfTy := some (.clsOf name)
      runtimeMain := false } }

theorem classBodyCtx_constGet {κ : Ctx} (hf : κ.frame = none) (name cn : String) :
    constGet? (classBodyCtx κ name) cn = constGet? κ cn := by
  simp only [constGet?, constPaths]
  rw [hf]
  rfl

end Ratchet
