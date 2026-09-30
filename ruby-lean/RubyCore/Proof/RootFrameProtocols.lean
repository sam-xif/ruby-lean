import RubyCore.Proof.RootFrameClosures

/-! Framing the native protocol entry points. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem procClosure_frame (K : List Kont) (m : Machine) (v : Value) :
    procClosure? (pushRootK K m) v = procClosure? m v := rfl

syntax "root_walk" ident ident : tactic
macro_rules
  | `(tactic| root_walk $K $hK) => `(tactic|
    ((try dsimp only) <;> (try simp (disch := assumption) only [rootFrameLem, Option.map_some, Option.map_none]) <;>
     first
       | rfl
       | (simp only [pushRootK, rootFrameR, withKont]; (repeat' split) <;> rfl)
       | (rw [← callClosure_frame $K]; congr 1;
          simp only [pushRootK]; (repeat' split) <;> rfl)
       | (split <;> root_walk $K $hK)
       | skip))

@[rootFrameLem] theorem raiseFrozen_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (recv : Value),
  Interp.raiseFrozen (pushRootK K m) recv = rootFrameR K (Interp.raiseFrozen m recv) := by
  intros
  unfold RubyCore.Interp.raiseFrozen
  root_walk K hK

@[rootFrameLem] theorem methodEditMiss_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (target : ObjId) (name : String) (removeOnly : Bool)
  (checkNative : optParam Bool Bool.true) (fallbackObject : optParam Bool Bool.false),
  Interp.methodEditMiss (pushRootK K m) target name removeOnly checkNative fallbackObject = rootFrameR K (Interp.methodEditMiss m target name removeOnly checkNative fallbackObject) := by
  intros
  unfold RubyCore.Interp.methodEditMiss
  root_walk K hK

@[rootFrameLem] theorem callObjectInspect_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  Interp.callObjectInspect (pushRootK K m) recv args kw = rootFrameR K (Interp.callObjectInspect m recv args kw) := by
  intros
  unfold RubyCore.Interp.callObjectInspect
  root_walk K hK

@[rootFrameLem] theorem continueArray_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (acc : List Value) (rest : List Expr),
  Interp.continueArray (pushRootK K m) acc rest = rootFrameR K (Interp.continueArray m acc rest) := by
  intros
  unfold RubyCore.Interp.continueArray
  root_walk K hK

@[rootFrameLem] theorem copyErrorNext_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (lead : String) (remaining : List Value) (parts : List String),
  Interp.copyErrorNext (pushRootK K m) lead remaining parts = rootFrameR K (Interp.copyErrorNext m lead remaining parts) := by
  intros
  unfold RubyCore.Interp.copyErrorNext
  root_walk K hK

@[rootFrameLem] theorem copyClassError_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (lead : String) (value : Value),
  Interp.copyClassError (pushRootK K m) lead value = rootFrameR K (Interp.copyClassError m lead value) := by
  intros
  unfold RubyCore.Interp.copyClassError
  root_walk K hK

@[rootFrameLem] theorem arrayInitYield_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (recv : ObjId) (block : Value) (index size : Nat),
  Interp.arrayInitYield (pushRootK K m) recv block index size = rootFrameR K (Interp.arrayInitYield m recv block index size) := by
  intros
  unfold RubyCore.Interp.arrayInitYield
  root_walk K hK

@[rootFrameLem] theorem callConstAdded_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (target : ObjId) (name : String),
  Interp.callConstAdded (pushRootK K m) target name = rootFrameR K (Interp.callConstAdded m target name) := by
  intros
  unfold RubyCore.Interp.callConstAdded
  root_walk K hK

@[rootFrameLem] theorem initializeInstance_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (inst : Value) (args : List Value) (blk : Option Value)
  (kw : List (Value × Value)),
  Interp.initializeInstance (pushRootK K m) inst args blk kw = rootFrameR K (Interp.initializeInstance m inst args blk kw) := by
  intros
  unfold RubyCore.Interp.initializeInstance
  root_walk K hK

@[rootFrameLem] theorem initializeModuleBlock_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (klass : ObjId) (blk : Option Value) (result : Value),
  Interp.initializeModuleBlock (pushRootK K m) klass blk result = rootFrameR K (Interp.initializeModuleBlock m klass blk result) := by
  intros
  unfold RubyCore.Interp.initializeModuleBlock
  root_walk K hK

@[rootFrameLem] theorem blockPassInvalid_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (call : ConversionCall) (source result : Value),
  Interp.blockPassInvalid (pushRootK K m) call source result = rootFrameR K (Interp.blockPassInvalid m call source result) := by
  intros
  unfold RubyCore.Interp.blockPassInvalid
  root_walk K hK

@[rootFrameLem] theorem constantNameTypeError_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (source : Value),
  Interp.constantNameTypeError (pushRootK K m) source = rootFrameR K (Interp.constantNameTypeError m source) := by
  intros
  unfold RubyCore.Interp.constantNameTypeError
  root_walk K hK

@[rootFrameLem] theorem classNameTypeError_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (klass : ObjId) (lead tail : String),
  Interp.classNameTypeError (pushRootK K m) klass lead tail = rootFrameR K (Interp.classNameTypeError m klass lead tail) := by
  intros
  unfold RubyCore.Interp.classNameTypeError
  root_walk K hK

@[rootFrameLem] theorem undefAliasMiss_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (name : String), Interp.undefAliasMiss (pushRootK K m) name = rootFrameR K (Interp.undefAliasMiss m name) := by
  intros
  unfold RubyCore.Interp.undefAliasMiss
  root_walk K hK

@[rootFrameLem] theorem enumMake_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (recv : Value) (name : String) (args : optParam (List Value) [])
  (size : optParam EnumSize EnumSize.unknown)
  (kw : optParam (List (Value × Value)) []),
  Interp.enumMake (pushRootK K m) recv name args size kw = rootFrameR K (Interp.enumMake m recv name args size kw) := by
  intros
  unfold RubyCore.Interp.enumMake
  root_walk K hK

@[rootFrameLem] theorem enumQueue_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (data : EnumData) (blk : Option Value),
  Interp.enumQueue (pushRootK K m) data blk = rootFrameR K (Interp.enumQueue m data blk) := by
  intros
  unfold RubyCore.Interp.enumQueue
  root_walk K hK

@[rootFrameLem] theorem enumArity_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (n : Nat) (expected : String),
  Interp.enumArity (pushRootK K m) n expected = rootFrameR K (Interp.enumArity m n expected) := by
  intros
  unfold RubyCore.Interp.enumArity
  root_walk K hK

@[rootFrameLem] theorem enumSizeValue_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (v : Value), Interp.enumSizeValue (pushRootK K m) v = (Interp.enumSizeValue m v).mapError (rootFrameR K) := by
  intros
  unfold RubyCore.Interp.enumSizeValue
  root_walk K hK

@[rootFrameLem] theorem finishNativeClone_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (copy original freeze : Value),
  Interp.finishNativeClone (pushRootK K m) copy original freeze = rootFrameR K (Interp.finishNativeClone m copy original freeze) := by
  intros
  unfold RubyCore.Interp.finishNativeClone
  root_walk K hK

@[rootFrameLem] theorem raiseConstantError_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (cls : ObjId) (text : String),
  Interp.raiseConstantError (pushRootK K m) cls text = rootFrameR K (Interp.raiseConstantError m cls text) := by
  intros
  unfold RubyCore.Interp.raiseConstantError
  root_walk K hK

@[rootFrameLem] theorem expandParamBindings_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (subs : List Param) (values : List Value)
  (remaining : List (Param × Value)) (body : Expr),
  Interp.expandParamBindings (pushRootK K m) subs values remaining body = rootFrameR K (Interp.expandParamBindings m subs values remaining body) := by
  intros
  unfold RubyCore.Interp.expandParamBindings
  root_walk K hK

#print axioms callClosure_frame
#print axioms finishNativeClone_frame
#print axioms expandParamBindings_frame
end RubyCore.Proof.Root
