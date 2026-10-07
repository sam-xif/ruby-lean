import Books.Metatheory.Framing.RootFrameSend

/-! Root-execution framing for the native inspection protocol. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 400000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem inspectAny_frame (K : List Kont)
    (m : Machine) (recv : Value) :
    (pushRootK K m).objectInspections.any (recv.identEq ·) =
    m.objectInspections.any (recv.identEq ·) := rfl

@[rootFrameLem] theorem continueObjectInspect_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv filter : Value) (remaining : List String) (text : String) :
    continueObjectInspect (pushRootK K m) recv filter remaining text =
      rootFrameR K (continueObjectInspect m recv filter remaining text) := by
  induction remaining generalizing m text with
  | nil =>
    change .next (withCtl (allocStr (pushRootK K m) ("#" ++ String.ofList (text.toList.drop 1) ++ ">")).2 (.value (allocStr (pushRootK K m) ("#" ++ String.ofList (text.toList.drop 1) ++ ">")).1)) =
      rootFrameR K (.next (withCtl (allocStr m ("#" ++ String.ofList (text.toList.drop 1) ++ ">")).2 (.value (allocStr m ("#" ++ String.ofList (text.toList.drop 1) ++ ">")).1)))
    simp only [rootFrameLem, rootFrameR]
  | cons name more ih =>
    rw [continueObjectInspect.eq_def, continueObjectInspect.eq_def]
    simp (disch := assumption) only [rootFrameLem, ih]
    root_native_walk K hK

@[rootFrameLem] theorem beginObjectInspect_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv filter : Value) :
    beginObjectInspect (pushRootK K m) recv filter = rootFrameR K (beginObjectInspect m recv filter) := by
  unfold beginObjectInspect
  simp only [rootFrameLem]
  root_native_walk K hK

@[rootFrameLem] theorem resumeObjectInspect_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv filter : Value) (remaining : List String)
    (text : String) (stringifying : Option Value) (value : Value) :
    resumeObjectInspect (pushRootK K m) recv filter remaining text stringifying value =
      rootFrameR K (resumeObjectInspect m recv filter remaining text stringifying value) := by
  have hLock := hK.hashLockFree
  unfold resumeObjectInspect
  root_native_walk K hK

#print axioms beginObjectInspect_frame
end RubyCore.Proof.Root
