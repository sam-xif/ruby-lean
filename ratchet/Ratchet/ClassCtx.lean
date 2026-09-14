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
      runtimeMain := false } }

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
