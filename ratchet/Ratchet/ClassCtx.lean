import Ratchet.Judge
import Ratchet.MethodCtx

/-! Enter the lexical scope of a fresh class, without advertising future methods. -/
namespace Ratchet

def classBodyCtx (κ : Ctx) (name : String) : Ctx :=
  { κ with
    scope := { κ.scope with
      frame := none
      blockTy := none
      selfTy := some (.clsOf name)
      runtimeMain := false
      runtimeClass := some name
      closedIvars := true } }

/-- A receiver annotation is an open field record, even when its constructor originally
knew a complete shape. Method bodies do not silently recover that erased information. -/
def instanceBodyCtx (κ : Ctx) (fr : Frame) (I : Ty) : Ctx :=
  { κ with scope := { κ.scope with
      frame := some fr
      blockTy := none
      selfTy := some (.inst fr.recvClass I)
      runtimeMain := false
      runtimeClass := some fr.defClass
      closedIvars := false } }

/-- Publish one executed definition, retaining earlier declarations. Admission must check
name freshness and the body; this updater never scans or advertises a future class body. -/
def classWithMethod (c : Cls) (d : Defn) : Cls := { c with methods := d :: c.methods }

def instanceDeclCtx (κ : Ctx) (c : Cls) (d : Defn) : Ctx :=
  { reserveNameCtx κ d.name with
    pos := { κ.pos with classes := classWithMethod c d :: κ.classes } }

theorem classBodyCtx_constGet {κ : Ctx} (hf : κ.frame = none) (name cn : String) :
    constGet? (classBodyCtx κ name) cn = constGet? κ cn := by
  simp only [constGet?, constPaths]
  rw [hf]
  rfl

end Ratchet
