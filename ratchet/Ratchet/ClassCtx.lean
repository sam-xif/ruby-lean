import Ratchet.Judge
import Ratchet.MethodCtx

/-! Enter the lexical scope of a fresh class, without advertising future methods. -/
namespace Ratchet

/-- Restore lexical activation only; executed declarations and weakened absence facts
belong to the outgoing body context, not to the saved caller. -/
def returnScopeCtx (caller body : Ctx) : Ctx := { body with scope := caller.scope }

def classBodyCtx (κ : Ctx) (name : String) : Ctx :=
  { κ with
    pos := { κ.pos with globalConsts := name :: κ.pos.globalConsts }
    scope := { κ.scope with
      frame := none
      blockTy := none
      selfTy := some (.clsOf name)
      runtimeMain := false
      runtimeClass := some name
      closedIvars := true } }

/-- Freshness is a static absence test backed by the interpreted global-name bound. -/
def freshClassNameB (κ : Ctx) (name : String) : Bool := !κ.pos.globalConsts.contains name

/-- The just-created ordinary class, before any body statement has executed. This records
no future methods and makes no claim about inherited initialize. -/
def classHeader (name : String) : Cls := ⟨name, none, [], [], false, [], [], []⟩

def classHeaderCtx (κ : Ctx) (name : String) : Ctx :=
  { κ with pos := { κ.pos with
      classes := classHeader name :: κ.classes
      plainAlloc := name :: κ.pos.plainAlloc } }

theorem classHeader_ancestors (C : CTable) (name : String) :
    ancestors? (classHeader name :: C) name = some [name] := by
  simp [ancestors?, ancestorsUp, clsGet?, classHeader, mixinAncestors?]

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

/-- Initializer entry has a freshly allocated receiver with a complete empty field set.
This stronger scope is established by allocation, not by an open instance annotation. -/
def initializerBodyCtx (κ : Ctx) (cn : String) : Ctx :=
  let body := instanceBodyCtx κ ⟨cn, cn, "initialize"⟩ .ivar0
  { body with scope := { body.scope with closedIvars := true } }

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
