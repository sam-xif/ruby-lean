import Books.Metatheory.Framing.RootFrameFrozen

/-! Root-execution framing for expression evaluation. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem lexicalConstant_frame (K : List Kont) (m : Machine) (name : String) :
    lexicalConstant (pushRootK K m) name = lexicalConstant m name := rfl

@[rootFrameLem] theorem unmodeledFeatureRoot_frame (K : List Kont) (m : Machine) (name : String) :
    unmodeledFeatureRoot (pushRootK K m) name = unmodeledFeatureRoot m name := rfl

@[rootFrameLem] theorem currentDefinitionFrame_frame (K : List Kont) (m : Machine) :
    (pushRootK K m).currentDefinitionFrame = m.currentDefinitionFrame := by
  simp only [Machine.currentDefinitionFrame, rootFrameLem]

@[rootFrameLem] theorem evalDefined_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (e : Expr) :
    evalDefined (pushRootK K m) e = rootFrameR K (evalDefined m e) := by
  have hLock := hK.hashLockFree
  cases e
  case var kind name =>
    cases kind <;> unfold evalDefined
    all_goals cases hg : matchGlobal m name <;>
      simp (disch := assumption) only [rootFrameLem, hg, Option.map_none, Option.map_some] <;>
      root_native_walk K hK
  all_goals unfold evalDefined <;> root_native_walk K hK

@[rootFrameLem] theorem evalExpr_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (e : Expr) :
    evalExpr (pushRootK K m) e = rootFrameR K (evalExpr m e) := by
  have hLock := hK.hashLockFree
  cases e
  case var kind name =>
    cases kind <;> unfold evalExpr
    all_goals cases hg : matchGlobal m name <;>
      simp (disch := assumption) only [rootFrameLem, hg, Option.map_none, Option.map_some] <;>
      root_native_walk K hK
  all_goals unfold evalExpr <;> root_native_walk K hK

#print axioms evalDefined_frame
#print axioms evalExpr_frame
end RubyCore.Proof.Root
