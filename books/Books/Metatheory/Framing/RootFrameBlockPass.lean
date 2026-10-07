import Books.Metatheory.Framing.RootFrameInspect

/-! Root-execution framing for block conversion and splat evaluation. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem resumeSplat_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (call : SplatCall) (values : List Value) :
    resumeSplat (pushRootK K m) call values = rootFrameR K (resumeSplat m call values) := by
  have hLock := hK.hashLockFree
  unfold resumeSplat
  root_native_walk K hK

@[rootFrameLem] theorem blockPassProc_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (v : Value) :
    blockPassProc (pushRootK K m) v = blockPassProc m v := by
  have hLock := hK.hashLockFree
  unfold blockPassProc
  root_native_walk K hK

@[rootFrameLem] theorem blockPassMethod_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (v : Value) (name : String) :
    blockPassMethod (pushRootK K m) v name = blockPassMethod m v name := by
  have hLock := hK.hashLockFree
  unfold blockPassMethod
  root_native_walk K hK

@[rootFrameLem] theorem blockPassNoConversion_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (call : ConversionCall) (source : Value) :
    blockPassNoConversion (pushRootK K m) call source = rootFrameR K (blockPassNoConversion m call source) := by
  have hLock := hK.hashLockFree
  unfold blockPassNoConversion
  root_native_walk K hK

@[rootFrameLem] theorem finishConversion_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (call : ConversionCall) (source result : Value)
    (direct : Bool) :
    finishConversion (pushRootK K m) call source result direct = rootFrameR K (finishConversion m call source result direct) := by
  have hLock := hK.hashLockFree
  unfold finishConversion
  root_native_walk K hK

@[rootFrameLem] theorem blockPassMissing_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (call : ConversionCall) (source : Value)
    (respond respondMissing : Bool) :
    blockPassMissing (pushRootK K m) call source respond respondMissing = rootFrameR K (blockPassMissing m call source respond respondMissing) := by
  have hLock := hK.hashLockFree
  unfold blockPassMissing
  root_native_walk K hK

@[rootFrameLem] theorem blockPassChecked_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (call : ConversionCall) (source : Value)
    (promised : Bool) :
    blockPassChecked (pushRootK K m) call source promised = rootFrameR K (blockPassChecked m call source promised) := by
  have hLock := hK.hashLockFree
  unfold blockPassChecked
  root_native_walk K hK

@[rootFrameLem] theorem blockPassRespond_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (call : ConversionCall) (source : Value)
    (md : MethodDef) :
    blockPassRespond (pushRootK K m) call source md = rootFrameR K (blockPassRespond m call source md) := by
  have hLock := hK.hashLockFree
  unfold blockPassRespond
  root_native_walk K hK

@[rootFrameLem] theorem startCheckedConversion_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (call : ConversionCall) (source : Value) :
    startCheckedConversion (pushRootK K m) call source = rootFrameR K (startCheckedConversion m call source) := by
  have hLock := hK.hashLockFree
  unfold startCheckedConversion
  root_native_walk K hK

@[rootFrameLem] theorem startSplat_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (call : SplatCall) (source : Value) :
    startSplat (pushRootK K m) call source = rootFrameR K (startSplat m call source) := by
  have hLock := hK.hashLockFree
  unfold startSplat
  root_native_walk K hK

@[rootFrameLem] theorem coerceBlockPass_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (call : BlockPassCall) (source : Value) :
    coerceBlockPass (pushRootK K m) call source = rootFrameR K (coerceBlockPass m call source) := by
  have hLock := hK.hashLockFree
  unfold coerceBlockPass
  root_native_walk K hK

@[rootFrameLem] theorem resumeBlockPass_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (call : ConversionCall) (source : Value)
    (phase : BlockPassPhase) (result : Value) :
    resumeBlockPass (pushRootK K m) call source phase result = rootFrameR K (resumeBlockPass m call source phase result) := by
  have hLock := hK.hashLockFree
  unfold resumeBlockPass
  root_native_walk K hK

@[rootFrameLem] theorem unwindBlockPass_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (call : ConversionCall) (source : Value)
    (phase : BlockPassPhase) (j : Jump) :
    unwindBlockPass (pushRootK K m) call source phase j = rootFrameR K (unwindBlockPass m call source phase j) := by
  have hLock := hK.hashLockFree
  unfold unwindBlockPass
  root_native_walk K hK


end RubyCore.Proof.Root
