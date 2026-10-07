import Books.Metatheory.Framing.RootFrameBlockPass

/-! Framing the native frozen-error protocol and continuation support. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 400000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem finishFrozen_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (exc message value : Value) :
    finishFrozen (pushRootK K m) exc message value = rootFrameR K (finishFrozen m exc message value) := by
  unfold finishFrozen
  root_native_walk K hK

@[rootFrameLem] theorem beginFrozenInit_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv name : Value) :
    beginFrozenInit (pushRootK K m) recv name = rootFrameR K (beginFrozenInit m recv name) := by
  unfold beginFrozenInit
  root_native_walk K hK

@[rootFrameLem] theorem resumeFrozen_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (phase : FrozenPhase) (value : Value) :
    resumeFrozen (pushRootK K m) recv phase value = rootFrameR K (resumeFrozen m recv phase value) := by
  have hLock := hK.hashLockFree
  unfold resumeFrozen
  simp only [rootFrameLem]
  root_native_walk K hK

@[rootFrameLem] theorem nextClause_root (K : List Kont) (hK : ContextFree K)
    (m : Machine) (node : BeginNode) (exc : Value)
    (clauses : List (List Expr × Option (TargetKind × String) × Expr)) :
    nextClause (pushRootK K m) node exc clauses = pushRootK K (nextClause m node exc clauses) := by
  induction clauses with
  | nil => rw [nextClause.eq_def, nextClause.eq_def]; root_native_walk K hK
  | cons cl rest ih =>
    rw [nextClause.eq_def, nextClause.eq_def]
    root_native_walk K hK
    all_goals exact ih

@[rootFrameLem] theorem undefNames_root (K : List Kont) (hK : ContextFree K)
    (m : Machine) (defmod : ObjId) (names : List String) :
    undefNames (pushRootK K m) defmod names = rootFrameR K (undefNames m defmod names) := by
  induction names generalizing m with
  | nil => rw [undefNames.eq_def, undefNames.eq_def]; root_native_walk K hK
  | cons name rest ih =>
    rw [undefNames.eq_def, undefNames.eq_def]
    root_native_walk K hK
    all_goals exact ih {m with heap := undefMethod m.heap defmod name}

theorem nextClause_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (node : BeginNode) (exc : Value)
    (clauses : List (List Expr × Option (TargetKind × String) × Expr)) :
    nextClause (pushRootK K m) node exc clauses = pushRootK K (nextClause m node exc clauses) :=
  nextClause_root K hK m node exc clauses

theorem undefNames_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (defmod : ObjId) (names : List String) :
    undefNames (pushRootK K m) defmod names = rootFrameR K (undefNames m defmod names) :=
  undefNames_root K hK m defmod names

#print axioms resumeFrozen_frame
#print axioms nextClause_frame
#print axioms undefNames_frame
end RubyCore.Proof.Root
