import RubyCore.Proof.RootFrameContext

/-! Framing activation entry, including shared for-loop locals and block scopes. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem definitionFrameId_frame (K : List Kont) (m : Machine) (fid : FrameId) :
    (pushRootK K m).definitionFrameId fid = m.definitionFrameId fid := by
  have hg : ∀ fuel fid, Machine.definitionFrameId.go (pushRootK K m) fuel fid =
      Machine.definitionFrameId.go m fuel fid := by
    intro fuel
    induction fuel with
    | zero => intro fid; rfl
    | succ n ih =>
      intro fid
      simp only [Machine.definitionFrameId.go, rootFrameLem]
      split <;> first | rfl | exact ih _
  exact hg _ _

@[rootFrameLem] theorem definitionFrameId_fun_frame (K : List Kont) (m : Machine) :
    (pushRootK K m).definitionFrameId = m.definitionFrameId :=
  funext (definitionFrameId_frame K m)

@[rootFrameLem] theorem queueParamBindings_frame (K : List Kont) (m : Machine)
    (pending : List (Param × Value)) (body : Expr) :
    queueParamBindings (pushRootK K m) pending body = pushRootK K (queueParamBindings m pending body) := by
  unfold queueParamBindings
  split <;> simp only [rootFrameLem]

@[rootFrameLem] theorem queueForAssignments_frame (K : List Kont) (m : Machine)
    (pending : List ((TargetKind × String) × Value)) (body : Expr) :
    queueForAssignments (pushRootK K m) pending body = pushRootK K (queueForAssignments m pending body) := by
  cases pending with
  | nil => rfl
  | cons p rest => cases ha : m.activeEnumerator <;> simp [queueForAssignments, pushRootK, ha]

@[rootFrameLem] theorem finishForBindings_frame (K : List Kont) (m : Machine)
    (targets : List (TargetKind × String)) (values : List Value) (body : Expr) :
    finishForBindings (pushRootK K m) targets values body = rootFrameR K (finishForBindings m targets values body) := by
  simp only [finishForBindings, rootFrameLem]

@[rootFrameLem] theorem startForBindings_frame (K : List Kont) (m : Machine)
    (targets : List (TargetKind × String)) (multiple : Bool) (args : List Value) (body : Expr) :
    startForBindings (pushRootK K m) targets multiple args body =
      rootFrameR K (startForBindings m targets multiple args body) := by
  unfold startForBindings
  root_simp
  root_arms

@[rootFrameLem] theorem enterForClosure_frame (K : List Kont) (m : Machine) (cl : Closure)
    (targets : List (TargetKind × String)) (args : List Value) (brk : Option FrameId)
    (selfOv : Option Value) (defmodOv : Option ObjId) :
    enterForClosure (pushRootK K m) cl targets args brk selfOv defmodOv =
      rootFrameR K (enterForClosure m cl targets args brk selfOv defmodOv) := by
  unfold enterForClosure
  simp only [rootFrameLem]
  refine Eq.trans ?_ (startForBindings_frame K _ _ _ _ _)
  congr 1
  cases ha : m.activeEnumerator <;> simp [pushRootK, ha]

@[rootFrameLem] theorem enterClosure_frame (K : List Kont) (m : Machine) (cl : Closure)
    (args : List Value) (brk : Option FrameId) (selfOv : Option Value) (defmodOv : Option ObjId) :
    enterClosure (pushRootK K m) cl args brk selfOv defmodOv =
      rootFrameR K (enterClosure m cl args brk selfOv defmodOv) := by
  unfold enterClosure
  root_simp
  root_arms
  all_goals (try (apply congrArg StepResult.next; refine Eq.trans ?_ (queueParamBindings_frame K _ _ _)))
  all_goals (try congr 1)
  all_goals (cases ha : m.activeEnumerator <;> simp_all [queueParamBindings, withCtl, withKont, pushRootK, allocArr, ha])
  all_goals (repeat' split) <;> simp_all [pushRootK, withKont, allocArr]

@[rootFrameLem] theorem callClosure_frame (K : List Kont)
    (m : Machine) (cl : Closure) (args : List Value) (brk : Option FrameId)
    (selfOv : Option Value) (defmodOv : Option ObjId) :
    callClosure (pushRootK K m) cl args brk selfOv defmodOv =
      rootFrameR K (callClosure m cl args brk selfOv defmodOv) := by
  unfold callClosure
  simp only [rootFrameLem]
  root_arms

@[rootFrameLem] theorem callProcBuiltin_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value) (kw : List (Value × Value)) :
    callProcBuiltin (pushRootK K m) recv args kw = rootFrameR K (callProcBuiltin m recv args kw) := by
  unfold callProcBuiltin
  simp only [callClosure_frame K, rootFrameLem]
  root_arms

end RubyCore.Proof.Root
