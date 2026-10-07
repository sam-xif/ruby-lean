import Books.Metatheory.Machine.NotDoneBase

/-! Every interpreter helper either advances the machine or reports an escape
or unsupported operation. The lemmas follow the helper call graph, so each proof
uses only its direct callees. `done_inv` below is the run-completion inversion. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
namespace RubyCore.Proof
open RubyCore.Interp RubyCore.Builtins

@[simp, ndLem] theorem classNameTypeError_notDone :
    ∀ (m : Machine) (klass : ObjId) (lead tail : String),
  isDone (Interp.classNameTypeError m klass lead tail) = false := by
  intros
  unfold RubyCore.Interp.classNameTypeError
  nd_walk

@[simp, ndLem] theorem raiseFrozen_notDone :
    ∀ (m : Machine) (recv : Value),
  isDone (Interp.raiseFrozen m recv) = false := by
  intros
  unfold RubyCore.Interp.raiseFrozen
  nd_walk

@[simp, ndLem] theorem constructResult_notDone :
    ∀ (a : BRes), isDone (Interp.constructResult a) = false := by
  intros
  unfold RubyCore.Interp.constructResult
  nd_walk

@[simp, ndLem] theorem enumArity_notDone :
    ∀ (m : Machine) (n : Nat) (expected : String),
  isDone (Interp.enumArity m n expected) = false := by
  intros
  unfold RubyCore.Interp.enumArity
  nd_walk

@[simp, ndLem] theorem callAllocate_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callAllocate m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callAllocate
  nd_walk

@[simp, ndLem] theorem enumMake_notDone :
    ∀ (m : Machine) (recv : Value) (name : String) (args : optParam (List Value) [])
  (size : optParam EnumSize EnumSize.unknown)
  (kw : optParam (List (Value × Value)) []),
  isDone (Interp.enumMake m recv name args size kw) = false := by
  intros
  unfold RubyCore.Interp.enumMake
  nd_walk

@[simp, ndLem] theorem enterClosure_notDone :
    ∀ (m : Machine) (cl : Closure) (args : List Value) (brk : Option FrameId)
  (selfOv : optParam (Option Value) Option.none) (defmodOv : optParam (Option ObjId) Option.none),
  isDone (Interp.enterClosure m cl args brk selfOv defmodOv) = false := by
  intros
  unfold RubyCore.Interp.enterClosure
  nd_walk

@[simp, ndLem] theorem finishForBindings_notDone :
    ∀ (m : Machine) (targets : List (TargetKind × String)) (values : List Value)
  (body : Expr), isDone (Interp.finishForBindings m targets values body) = false := by
  intros
  unfold RubyCore.Interp.finishForBindings
  nd_walk

@[simp, ndLem] theorem startForBindings_notDone :
    ∀ (m : Machine) (targets : List (TargetKind × String)) (multiple : Bool) (args : List Value)
  (body : Expr),
  isDone (Interp.startForBindings m targets multiple args body) = false := by
  intros
  unfold RubyCore.Interp.startForBindings
  nd_walk

@[simp, ndLem] theorem enterForClosure_notDone :
    ∀ (m : Machine) (cl : Closure) (targets : List (TargetKind × String))
  (args : List Value) (brk : Option FrameId) (selfOv : Option Value)
  (defmodOv : Option ObjId),
  isDone (Interp.enterForClosure m cl targets args brk selfOv defmodOv) = false := by
  intros
  unfold RubyCore.Interp.enterForClosure
  nd_walk

@[simp, ndLem] theorem suspendEnumerator_notDone :
    ∀ (m : Machine) (o : ObjId) (args : List Value),
  isDone (Interp.suspendEnumerator m o args) = false := by
  intros
  unfold RubyCore.Interp.suspendEnumerator
  nd_walk

@[simp, ndLem] theorem callClosure_notDone :
    ∀ (m : Machine) (cl : Closure) (args : List Value) (brk : Option FrameId)
  (selfOv : optParam (Option Value) Option.none) (defmodOv : optParam (Option ObjId) Option.none),
  isDone (Interp.callClosure m cl args brk selfOv defmodOv) = false := by
  intros
  unfold RubyCore.Interp.callClosure
  nd_walk

@[simp, ndLem] theorem iterStep_notDone :
    ∀ (m : Machine) (cl : Closure) (brk : FrameId) (rest : List (List Value))
  (kind : IterKind) (acc : List Value) (retVal : Value),
  isDone (Interp.iterStep m cl brk rest kind acc retVal) = false := by
  intros
  unfold RubyCore.Interp.iterStep
  nd_walk

@[simp, ndLem] theorem startIter_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (cl : Closure)
  (elemArgs : List (List Value)) (kind : IterKind) (initAcc : List Value)
  (retVal : Value),
  isDone (Interp.startIter m recv mname cl elemArgs kind initAcc retVal) = false := by
  intros
  unfold RubyCore.Interp.startIter
  nd_walk

@[simp, ndLem] theorem callArrayMapBuiltin_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (blk : Option Value) (kw : List (Value × Value)),
  isDone (Interp.callArrayMapBuiltin m recv mname args blk kw) = false := by
  intros
  unfold RubyCore.Interp.callArrayMapBuiltin
  nd_walk

@[simp, ndLem] theorem inheritableClass_notDone :
    ∀ (m : Machine) (value : Value) (requireInitialized : Bool),
  isDoneE (Interp.inheritableClass m value requireInitialized) = false := by
  intros
  unfold RubyCore.Interp.inheritableClass
  nd_walk

@[simp, ndLem] theorem callClassInitialize_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value) (blk : Option Value)
  (kw : List (Value × Value)),
  isDone (Interp.callClassInitialize m recv args blk kw) = false := by
  intros
  unfold RubyCore.Interp.callClassInitialize
  nd_walk

@[simp, ndLem] theorem callConstAdded_notDone :
    ∀ (m : Machine) (target : ObjId) (name : String),
  isDone (Interp.callConstAdded m target name) = false := by
  intros
  unfold RubyCore.Interp.callConstAdded
  nd_walk

@[simp, ndLem] theorem assignConstant_notDone :
    ∀ (m : Machine) (target : ObjId) (name : String) (value : Value),
  isDone (Interp.assignConstant m target name value) = false := by
  intros
  unfold RubyCore.Interp.assignConstant
  nd_walk

@[simp, ndLem] theorem raiseConstantError_notDone :
    ∀ (m : Machine) (cls : ObjId) (text : String),
  isDone (Interp.raiseConstantError m cls text) = false := by
  intros
  unfold RubyCore.Interp.raiseConstantError
  nd_walk

@[simp, ndLem] theorem finishConstantSet_notDone :
    ∀ (m : Machine) (target : ObjId) (value nameArg : Value),
  isDone (Interp.finishConstantSet m target value nameArg) = false := by
  intros
  unfold RubyCore.Interp.finishConstantSet
  nd_walk

@[simp, ndLem] theorem callConstSet_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callConstSet m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callConstSet
  nd_walk

@[simp, ndLem] theorem initializeInstance_notDone :
    ∀ (m : Machine) (inst : Value) (args : List Value) (blk : Option Value)
  (kw : List (Value × Value)),
  isDone (Interp.initializeInstance m inst args blk kw) = false := by
  intros
  unfold RubyCore.Interp.initializeInstance
  nd_walk

@[simp, ndLem] theorem legacyConstruct_notDone :
    ∀ (m : Machine) (recv : Value) (klass : ObjId) (args : List Value)
  (_blk : Option Value) (kw : List (Value × Value)),
  isDone (Interp.legacyConstruct m recv klass args _blk kw) = false := by
  intros
  unfold RubyCore.Interp.legacyConstruct
  nd_walk

@[simp, ndLem] theorem callConstruct_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value) (blk : Option Value)
  (kw : List (Value × Value)),
  isDone (Interp.callConstruct m recv args blk kw) = false := by
  intros
  fun_cases RubyCore.Interp.callConstruct <;> nd_walk

@[simp, ndLem] theorem finishCoreCopy_notDone :
    ∀ (m : Machine) (kind : ObjId) (recv source : Value),
  isDone (Interp.finishCoreCopy m kind recv source) = false := by
  intros
  unfold RubyCore.Interp.finishCoreCopy
  nd_walk

@[simp, ndLem] theorem callCoreCopy_notDone :
    ∀ (m : Machine) (kind : ObjId) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callCoreCopy m kind recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callCoreCopy
  nd_walk

@[simp, ndLem] theorem arrayInitYield_notDone :
    ∀ (m : Machine) (recv : ObjId) (block : Value) (index size : Nat),
  isDone (Interp.arrayInitYield m recv block index size) = false := by
  intros
  unfold RubyCore.Interp.arrayInitYield
  nd_walk

@[simp, ndLem] theorem callCoreInitialize_notDone :
    ∀ (m : Machine) (bid : String) (recv : Value) (args : List Value)
  (blk : Option Value) (kw : List (Value × Value)),
  isDone (Interp.callCoreInitialize m bid recv args blk kw) = false := by
  intros
  fun_cases RubyCore.Interp.callCoreInitialize <;> (try simp only [ndLem, ite_self])
  rename_i valid result hvalid
  have hnd : isDoneE valid = false := by
    dsimp only [valid]
    (repeat' split) <;> rfl
  exact isDone_of_excNotDone hvalid hnd

@[simp, ndLem] theorem enumSizeValue_notDone :
    ∀ (m : Machine) (v : Value), isDoneE (Interp.enumSizeValue m v) = false := by
  intros
  unfold RubyCore.Interp.enumSizeValue
  nd_walk

@[simp, ndLem] theorem enumInitialize_notDone :
    ∀ (m : Machine) (o : ObjId) (bid : String) (args : List Value) (blk : Option Value),
  isDone (Interp.enumInitialize m o bid args blk) = false := by
  intros
  unfold RubyCore.Interp.enumInitialize
  nd_walk

@[simp, ndLem] theorem enumQueue_notDone :
    ∀ (m : Machine) (data : EnumData) (blk : Option Value),
  isDone (Interp.enumQueue m data blk) = false := by
  intros
  unfold RubyCore.Interp.enumQueue
  nd_walk

@[simp, ndLem] theorem newStop_notDone :
    ∀ (m : Machine) (owner : Option ObjId) (result message : Value),
  isDone (Interp.newStop m owner result message) = false := by
  intros
  unfold RubyCore.Interp.newStop
  nd_walk

@[simp, ndLem] theorem enumStop_notDone :
    ∀ (m : Machine) (original : Value),
  isDone (Interp.enumStop m original) = false := by
  intros
  unfold RubyCore.Interp.enumStop
  nd_walk

@[simp, ndLem] theorem enumNext_notDone :
    ∀ (m : Machine) (o : ObjId) (peek values : Bool),
  isDone (Interp.enumNext m o peek values) = false := by
  intros
  unfold RubyCore.Interp.enumNext
  nd_walk

@[simp, ndLem] theorem callEnumerator_notDone :
    ∀ (m : Machine) (bid : String) (recv : Value) (args : List Value)
  (blk : Option Value) (kw : List (Value × Value)),
  isDone (Interp.callEnumerator m bid recv args blk kw) = false := by
  intros
  fun_cases RubyCore.Interp.callEnumerator <;> nd_walk

@[simp, ndLem] theorem callExceptionCopy_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callExceptionCopy m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callExceptionCopy
  nd_walk

@[simp, ndLem] theorem callExceptionMessage_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callExceptionMessage m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callExceptionMessage
  nd_walk

@[simp, ndLem] theorem enterUserMethod_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (md : MethodDef) (args : List Value)
  (blk : Option Value) (kw : optParam (List (Value × Value)) []),
  isDone (Interp.enterUserMethod m recv mname md args blk kw) = false := by
  intros
  fun_cases RubyCore.Interp.enterUserMethod <;> nd_walk

@[simp, ndLem] theorem tryMixin_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value),
  isDoneO (Interp.tryMixin m recv mname args) = false := by
  intros
  unfold RubyCore.Interp.tryMixin
  nd_walk

@[simp, ndLem] theorem finishMethodEdit_notDone :
    ∀ (m : Machine) (target : ObjId) (event name : String) (remaining : List MethodEdit)
  (result : Value),
  isDone (Interp.finishMethodEdit m target event name remaining result) = false := by
  intros
  unfold RubyCore.Interp.finishMethodEdit
  nd_walk

@[simp, ndLem] theorem methodEditMiss_notDone :
    ∀ (m : Machine) (target : ObjId) (name : String) (removeOnly : Bool)
  (checkNative : optParam Bool Bool.true) (fallbackObject : optParam Bool false),
  isDone (Interp.methodEditMiss m target name removeOnly checkNative fallbackObject) =
    false := by
  intros
  unfold RubyCore.Interp.methodEditMiss
  nd_walk

@[simp, ndLem] theorem runMethodEdits_notDone :
    ∀ (m : Machine) (edits : List MethodEdit) (result : Value),
  isDone (Interp.runMethodEdits m edits result) = false := by
  intros
  unfold RubyCore.Interp.runMethodEdits
  nd_walk

@[simp, ndLem] theorem reflectAliasMethod_notDone :
    ∀ (m : Machine) (recv : Value) (_mname : String) (args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectAliasMethod m recv _mname args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectAliasMethod
  nd_walk

@[simp, ndLem] theorem reflectAttr_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectAttr m recv mname args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectAttr
  nd_walk

@[simp, ndLem] theorem reflectCatch_notDone :
    ∀ (m : Machine) (_recv : Value) (_mname : String) (args : List Value)
  (blk : Option Value),
  isDoneO (Interp.reflectCatch m _recv _mname args blk) = false := by
  intros
  unfold RubyCore.Interp.reflectCatch
  nd_walk

@[simp, ndLem] theorem reflectConstGet_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectConstGet m recv mname args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectConstGet
  nd_walk

@[simp, ndLem] theorem reflectDefineMethod_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (blk : Option Value),
  isDoneO (Interp.reflectDefineMethod m recv mname args blk) = false := by
  intros
  unfold RubyCore.Interp.reflectDefineMethod
  nd_walk

@[simp, ndLem] theorem reflectEval_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (blk : Option Value), isDoneO (Interp.reflectEval m recv mname args blk) = false := by
  intros
  unfold RubyCore.Interp.reflectEval
  nd_walk

@[simp, ndLem] theorem reflectIvarGet_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectIvarGet m recv mname args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectIvarGet
  nd_walk

@[simp, ndLem] theorem reflectIvarNames_notDone :
    ∀ (m : Machine) (recv : Value) (_mname : String) (_args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectIvarNames m recv _mname _args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectIvarNames
  nd_walk

@[simp, ndLem] theorem reflectIvarSet_notDone :
    ∀ (m : Machine) (recv : Value) (_mname : String) (args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectIvarSet m recv _mname args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectIvarSet
  nd_walk

@[simp, ndLem] theorem reflectMethodDefined_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectMethodDefined m recv mname args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectMethodDefined
  nd_walk

@[simp, ndLem] theorem reflectRemoveMethod_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectRemoveMethod m recv mname args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectRemoveMethod
  nd_walk

@[simp, ndLem] theorem reflectRespondTo_notDone :
    ∀ (m : Machine) (recv : Value) (_mname : String) (args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectRespondTo m recv _mname args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectRespondTo
  nd_walk

@[simp, ndLem] theorem reflectSingletonClass_notDone :
    ∀ (m : Machine) (recv : Value) (_mname : String) (_args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectSingletonClass m recv _mname _args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectSingletonClass
  nd_walk

@[simp, ndLem] theorem reflectThrow_notDone :
    ∀ (m : Machine) (_recv : Value) (_mname : String) (args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectThrow m _recv _mname args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectThrow
  nd_walk

@[simp, ndLem] theorem reflectVisibility_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (_blk : Option Value),
  isDoneO (Interp.reflectVisibility m recv mname args _blk) = false := by
  intros
  unfold RubyCore.Interp.reflectVisibility
  nd_walk

@[simp, ndLem] theorem tryReflect_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (blk : Option Value), isDoneO (Interp.tryReflect m recv mname args blk) = false := by
  intros
  unfold RubyCore.Interp.tryReflect
  nd_walk

@[simp, ndLem] theorem callMainMethod_notDone :
    ∀ (m : Machine) (recv : Value) (bid : String) (args : List Value)
  (blk : Option Value), isDone (Interp.callMainMethod m recv bid args blk) = false := by
  intros
  unfold RubyCore.Interp.callMainMethod
  nd_walk

@[simp, ndLem] theorem initializeModuleBlock_notDone :
    ∀ (m : Machine) (klass : ObjId) (blk : Option Value) (result : Value),
  isDone (Interp.initializeModuleBlock m klass blk result) = false := by
  intros
  unfold RubyCore.Interp.initializeModuleBlock
  nd_walk

@[simp, ndLem] theorem callModuleInitialize_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value) (blk : Option Value)
  (kw : List (Value × Value)),
  isDone (Interp.callModuleInitialize m recv args blk kw) = false := by
  intros
  unfold RubyCore.Interp.callModuleInitialize
  nd_walk

@[simp, ndLem] theorem copyClassError_notDone :
    ∀ (m : Machine) (lead : String) (value : Value),
  isDone (Interp.copyClassError m lead value) = false := by
  intros
  unfold RubyCore.Interp.copyClassError
  nd_walk

@[simp, ndLem] theorem finishNativeClone_notDone :
    ∀ (m : Machine) (copy original freeze : Value),
  isDone (Interp.finishNativeClone m copy original freeze) = false := by
  intros
  unfold RubyCore.Interp.finishNativeClone
  nd_walk

@[simp, ndLem] theorem beginNativeCopy_notDone :
    ∀ (m : Machine) (recv : Value) (clone : Bool) (freeze : Value),
  isDone (Interp.beginNativeCopy m recv clone freeze) = false := by
  intros
  unfold RubyCore.Interp.beginNativeCopy
  nd_walk

@[simp, ndLem] theorem copyErrorNext_notDone :
    ∀ (m : Machine) (lead : String) (remaining : List Value) (parts : List String),
  isDone (Interp.copyErrorNext m lead remaining parts) = false := by
  intros
  unfold RubyCore.Interp.copyErrorNext
  nd_walk

@[simp, ndLem] theorem copyFreezeOption_notDone :
    ∀ (m : Machine) (kw : List (Value × Value)),
  isDoneE (Interp.copyFreezeOption m kw) = false := by
  intros
  unfold RubyCore.Interp.copyFreezeOption
  nd_walk

@[simp, ndLem] theorem callNativeClone_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callNativeClone m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callNativeClone
  nd_walk

@[simp, ndLem] theorem callNativeDup_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callNativeDup m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callNativeDup
  nd_walk

@[simp, ndLem] theorem callNativeInitializeClone_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callNativeInitializeClone m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callNativeInitializeClone
  nd_walk

@[simp, ndLem] theorem callNativeInitializeDup_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callNativeInitializeDup m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callNativeInitializeDup
  nd_walk

@[simp, ndLem] theorem tryIterator_notDone :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (blk : Option Value), isDoneO (Interp.tryIterator m recv mname args blk) = false := by
  intros
  unfold RubyCore.Interp.tryIterator
  nd_walk

@[simp, ndLem] theorem callNativeIterator_notDone :
    ∀ (m : Machine) (bid : String) (recv : Value) (args : List Value)
  (blk : Option Value) (kw : List (Value × Value)),
  isDone (Interp.callNativeIterator m bid recv args blk kw) = false := by
  intros
  unfold RubyCore.Interp.callNativeIterator
  nd_walk

@[simp, ndLem] theorem callObjectInspect_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callObjectInspect m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callObjectInspect
  nd_walk

@[simp, ndLem] theorem callProcBuiltin_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callProcBuiltin m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callProcBuiltin
  nd_walk

@[simp, ndLem] theorem raiseString_notDone :
    ∀ (m : Machine) (message : Value),
  isDone (Interp.raiseString m message) = false := by
  intros
  unfold RubyCore.Interp.raiseString
  nd_walk

@[simp, ndLem] theorem callRaise_notDone :
    ∀ (m : Machine) (args : List Value) (kw : List (Value × Value)),
  isDone (Interp.callRaise m args kw) = false := by
  intros
  unfold RubyCore.Interp.callRaise
  nd_walk

@[simp, ndLem] theorem callRequire_notDone :
    ∀ (m : Machine) (bid : String) (args : List Value) (kw : List (Value × Value)),
  isDone (Interp.callRequire m bid args kw) = false := by
  intros
  fun_cases RubyCore.Interp.callRequire <;> nd_walk

@[simp, ndLem] theorem callStringPlusBuiltin_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callStringPlusBuiltin m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callStringPlusBuiltin
  nd_walk

@[simp, ndLem] theorem callUncaughtMessage_notDone :
    ∀ (m : Machine) (recv : Value) (args : List Value)
  (kw : List (Value × Value)),
  isDone (Interp.callUncaughtMessage m recv args kw) = false := by
  intros
  unfold RubyCore.Interp.callUncaughtMessage
  nd_walk

@[simp, ndLem] theorem compileForwardable_notDone :
    ∀ (m : Machine) (args : List Value),
  isDone (Interp.compileForwardable m args) = false := by
  intros
  unfold RubyCore.Interp.compileForwardable
  nd_walk

@[simp, ndLem] theorem invokeMethodMissing_notDone :
    ∀ (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
  (args : List Value) (blk : Option Value)
  (reason :
    optParam MissingReason
      (if (implicit == SendSite.vcall) = Bool.true then MissingReason.vcall
      else MissingReason.ordinary))
  (kw : optParam (List (Value × Value)) []),
  isDone (Interp.invokeMethodMissing m recv implicit mname args blk reason kw) = false := by
  intros
  unfold RubyCore.Interp.invokeMethodMissing
  nd_walk

@[simp, ndLem] theorem dispatchMiss_notDone :
    ∀ (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
  (args : List Value) (blk : Option Value)
  (kw : optParam (List (Value × Value)) []),
  isDone (Interp.dispatchMiss m recv implicit mname args blk kw) = false := by
  intros
  unfold RubyCore.Interp.dispatchMiss
  nd_walk

@[simp, ndLem] theorem visError?_notDone :
    ∀ (m : Machine) (recv : Value) (site : SendSite) (md : MethodDef) (mname : String),
  isDoneO (Interp.visError? m recv site md mname) = false := by
  intros
  unfold RubyCore.Interp.visError?
  nd_walk

@[simp, ndLem] theorem invokeDispatch_notDone :
    ∀ (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
  (args : List Value) (blk : Option Value) (kw : List (Value × Value)),
  isDone (Interp.invoke.invokeDispatch m recv implicit mname args blk kw) = false := by
  intros
  fun_cases RubyCore.Interp.invoke.invokeDispatch <;> nd_walk

@[simp, ndLem] theorem invoke_notDone :
    ∀ (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
  (args : List Value) (blk : Option Value)
  (kw : optParam (List (Value × Value)) []),
  isDone (Interp.invoke m recv implicit mname args blk kw) = false := by
  intros
  fun_induction RubyCore.Interp.invoke <;> nd_walk

@[simp, ndLem] theorem continueObjectInspect_notDone :
    ∀ (m : Machine) (recv filter : Value) (remaining : List String) (text : String),
  isDone (Interp.continueObjectInspect m recv filter remaining text) = false := by
  intros
  fun_induction RubyCore.Interp.continueObjectInspect <;> nd_walk

@[simp, ndLem] theorem beginObjectInspect_notDone :
    ∀ (m : Machine) (recv filter : Value),
  isDone (Interp.beginObjectInspect m recv filter) = false := by
  intros
  unfold RubyCore.Interp.beginObjectInspect
  nd_walk

@[simp, ndLem] theorem constantNameTypeError_notDone :
    ∀ (m : Machine) (source : Value),
  isDone (Interp.constantNameTypeError m source) = false := by
  intros
  unfold RubyCore.Interp.constantNameTypeError
  nd_walk

@[simp, ndLem] theorem expandParamBindings_notDone :
    ∀ (m : Machine) (subs : List Param) (values : List Value)
  (remaining : List (Param × Value)) (body : Expr),
  isDone (Interp.expandParamBindings m subs values remaining body) = false := by
  intros
  unfold RubyCore.Interp.expandParamBindings
  nd_walk

@[simp, ndLem] theorem continueArray_notDone :
    ∀ (m : Machine) (acc : List Value) (rest : List Expr),
  isDone (Interp.continueArray m acc rest) = false := by
  intros
  unfold RubyCore.Interp.continueArray
  nd_walk

@[simp, ndLem] theorem finishSend_notDone :
    ∀ (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
  (args : List Value) (pblk : PendingBlk) (kw : optParam (List (Value × Value)) []),
  isDone (Interp.finishSend m recv implicit mname args pblk kw) = false := by
  intros
  unfold RubyCore.Interp.finishSend
  nd_walk

@[simp, ndLem] theorem startKwargs_notDone :
    ∀ (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
  (posArgs : List Value) (kwacc : List (Value × Value)) (entries : List KwEntry)
  (pblk : PendingBlk),
  isDone (Interp.startKwargs m recv implicit mname posArgs kwacc entries pblk) = false := by
  intros
  unfold RubyCore.Interp.startKwargs
  nd_walk

@[simp, ndLem] theorem startArgs_notDone :
    ∀ (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
  (acc : List Value) (rest : List Expr) (pblk : PendingBlk),
  isDone (Interp.startArgs m recv implicit mname acc rest pblk) = false := by
  intros
  unfold RubyCore.Interp.startArgs
  nd_walk

@[simp, ndLem] theorem doSuper_notDone :
    ∀ (m : Machine) (args : List Value) (blk : Option Value)
  (kw : optParam (List (Value × Value)) []),
  isDone (Interp.doSuper m args blk kw) = false := by
  intros
  fun_cases RubyCore.Interp.doSuper <;> nd_walk

@[simp, ndLem] theorem startSuperArgs_notDone :
    ∀ (m : Machine) (acc : List Value) (rest : List Expr) (blk : Option Value),
  isDone (Interp.startSuperArgs m acc rest blk) = false := by
  intros
  unfold RubyCore.Interp.startSuperArgs
  nd_walk

@[simp, ndLem] theorem doYield_notDone :
    ∀ (m : Machine) (args : List Value),
  isDone (Interp.doYield m args) = false := by
  intros
  unfold RubyCore.Interp.doYield
  nd_walk

@[simp, ndLem] theorem startYield_notDone :
    ∀ (m : Machine) (acc : List Value) (rest : List Expr),
  isDone (Interp.startYield m acc rest) = false := by
  intros
  unfold RubyCore.Interp.startYield
  nd_walk

@[simp, ndLem] theorem resumeSplat_notDone :
    ∀ (m : Machine) (call : SplatCall) (values : List Value),
  isDone (Interp.resumeSplat m call values) = false := by
  intros
  unfold RubyCore.Interp.resumeSplat
  nd_walk

@[simp, ndLem] theorem blockPassNoConversion_notDone :
    ∀ (m : Machine) (call : ConversionCall) (source : Value),
  isDone (Interp.blockPassNoConversion m call source) = false := by
  intros
  unfold RubyCore.Interp.blockPassNoConversion
  nd_walk

@[simp, ndLem] theorem blockPassMissing_notDone :
    ∀ (m : Machine) (call : ConversionCall) (source : Value) (respond respondMissing : Bool),
  isDone (Interp.blockPassMissing m call source respond respondMissing) = false := by
  intros
  unfold RubyCore.Interp.blockPassMissing
  nd_walk

@[simp, ndLem] theorem blockPassChecked_notDone :
    ∀ (m : Machine) (call : ConversionCall) (source : Value) (promised : Bool),
  isDone (Interp.blockPassChecked m call source promised) = false := by
  intros
  unfold RubyCore.Interp.blockPassChecked
  nd_walk

@[simp, ndLem] theorem invokeQueued_notDone :
    ∀ (m : Machine) (recv : Value) (site : SendSite) (name : String) (args : List Value)
  (blk : Option Value) (kw : List (Value × Value)),
  isDone (Interp.invokeQueued m recv site name args blk kw) = false := by
  intros
  unfold RubyCore.Interp.invokeQueued
  nd_walk

@[simp, ndLem] theorem evalDefined_notDone :
    ∀ (m : Machine) (e : Expr), isDone (Interp.evalDefined m e) = false := by
  intros
  unfold RubyCore.Interp.evalDefined
  nd_walk

@[simp, ndLem] theorem beginFrozenInit_notDone :
    ∀ (m : Machine) (recv name : Value),
  isDone (Interp.beginFrozenInit m recv name) = false := by
  intros
  unfold RubyCore.Interp.beginFrozenInit
  nd_walk

@[simp, ndLem] theorem finishFrozen_notDone :
    ∀ (m : Machine) (exc message value : Value),
  isDone (Interp.finishFrozen m exc message value) = false := by
  intros
  unfold RubyCore.Interp.finishFrozen
  nd_walk

@[simp, ndLem] theorem resumeFrozen_notDone :
    ∀ (m : Machine) (recv : Value) (phase : FrozenPhase) (value : Value),
  isDone (Interp.resumeFrozen m recv phase value) = false := by
  intros
  unfold RubyCore.Interp.resumeFrozen
  nd_walk

@[simp, ndLem] theorem blockPassInvalid_notDone :
    ∀ (m : Machine) (call : ConversionCall) (source result : Value),
  isDone (Interp.blockPassInvalid m call source result) = false := by
  intros
  unfold RubyCore.Interp.blockPassInvalid
  nd_walk

@[simp, ndLem] theorem finishConversion_notDone :
    ∀ (m : Machine) (call : ConversionCall) (source result : Value) (direct : Bool),
  isDone (Interp.finishConversion m call source result direct) = false := by
  intros
  unfold RubyCore.Interp.finishConversion
  nd_walk

@[simp, ndLem] theorem blockPassRespond_notDone :
    ∀ (m : Machine) (call : ConversionCall) (source : Value) (md : MethodDef),
  isDone (Interp.blockPassRespond m call source md) = false := by
  intros
  unfold RubyCore.Interp.blockPassRespond
  nd_walk

@[simp, ndLem] theorem startCheckedConversion_notDone :
    ∀ (m : Machine) (call : ConversionCall) (source : Value),
  isDone (Interp.startCheckedConversion m call source) = false := by
  intros
  unfold RubyCore.Interp.startCheckedConversion
  nd_walk

@[simp, ndLem] theorem resumeBlockPass_notDone :
    ∀ (m : Machine) (call : ConversionCall) (source : Value) (phase : BlockPassPhase)
  (result : Value),
  isDone (Interp.resumeBlockPass m call source phase result) = false := by
  intros
  unfold RubyCore.Interp.resumeBlockPass
  nd_walk

@[simp, ndLem] theorem missNoMethod_notDone :
    ∀ (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
  (_args : List Value),
  isDone (Interp.missNoMethod m recv implicit mname _args) = false := by
  intros
  unfold RubyCore.Interp.missNoMethod
  nd_walk

@[simp, ndLem] theorem arrayInitNext_notDone :
    ∀ (m : Machine) (recv : ObjId) (block : Value) (index size : Nat) (v : Value),
  isDone (Interp.arrayInitNext m recv block index size v) = false := by
  intros
  unfold RubyCore.Interp.arrayInitNext
  nd_walk

@[simp, ndLem] theorem finishClassInitialize_notDone :
    ∀ (m : Machine) (klass : ObjId) (blk : Option Value),
  isDone (Interp.finishClassInitialize m klass blk) = false := by
  intros
  unfold RubyCore.Interp.finishClassInitialize
  nd_walk

@[simp, ndLem] theorem finishUncaughtInspect_notDone :
    ∀ (m : Machine) (source : Option Value) (v : Value),
  isDone (Interp.finishUncaughtInspect m source v) = false := by
  intros
  unfold RubyCore.Interp.finishUncaughtInspect
  nd_walk

@[simp, ndLem] theorem pushClassFrame_notDone :
    ∀ (m : Machine) (k : ObjId) (libraryName : String) (body : Expr),
  isDone (Interp.pushClassFrame m k libraryName body) = false := by
  intros
  unfold RubyCore.Interp.pushClassFrame
  nd_walk

@[simp, ndLem] theorem enterClassBody_notDone :
    ∀ (m : Machine) (name : String) (isMod : Bool) (sup? : Option ObjId) (body : Expr),
  isDone (Interp.enterClassBody m name isMod sup? body) = false := by
  intros
  unfold RubyCore.Interp.enterClassBody
  nd_walk

@[simp, ndLem] theorem doReturn_notDone :
    ∀ (m : Machine) (v : Value), isDone (Interp.doReturn m v) = false := by
  intros
  unfold RubyCore.Interp.doReturn
  nd_walk

@[simp, ndLem] theorem evalExpr_notDone :
    ∀ (m : Machine) (e : Expr), isDone (Interp.evalExpr m e) = false := by
  intros
  unfold RubyCore.Interp.evalExpr
  nd_walk

@[simp, ndLem] theorem finishCopyError_notDone :
    ∀ (m : Machine) (lead : String) (remaining : List Value) (parts : List String)
  (fallback : Option Value) (value : Value),
  isDone (Interp.finishCopyError m lead remaining parts fallback value) = false := by
  intros
  unfold RubyCore.Interp.finishCopyError
  nd_walk

@[simp, ndLem] theorem coerceBlockPass_notDone :
    ∀ (m : Machine) (call : BlockPassCall) (source : Value),
  isDone (Interp.coerceBlockPass m call source) = false := by
  intros
  unfold RubyCore.Interp.coerceBlockPass
  nd_walk

@[simp, ndLem] theorem finishEnumerator_notDone :
    ∀ (m : Machine) (o : ObjId) (result : Value),
  isDone (Interp.finishEnumerator m o result) = false := by
  intros
  unfold RubyCore.Interp.finishEnumerator
  nd_walk

@[simp, ndLem] theorem finishConstantNameError_notDone :
    ∀ (m : Machine) (source : Option Value) (value : Value),
  isDone (Interp.finishConstantNameError m source value) = false := by
  intros
  unfold RubyCore.Interp.finishConstantNameError
  nd_walk

@[simp, ndLem] theorem startSplat_notDone :
    ∀ (m : Machine) (call : SplatCall) (source : Value),
  isDone (Interp.startSplat m call source) = false := by
  intros
  unfold RubyCore.Interp.startSplat
  nd_walk

@[simp, ndLem] theorem inheritClassBody_notDone :
    ∀ (m : Machine) (k : ObjId) (superclass : Option ObjId) (libraryName : String)
  (body : Expr),
  isDone (Interp.inheritClassBody m k superclass libraryName body) = false := by
  intros
  unfold RubyCore.Interp.inheritClassBody
  nd_walk

@[simp, ndLem] theorem enterScopedClassBody_notDone :
    ∀ (m : Machine) (container : ObjId) (name : String) (isMod : Bool) (body : Expr),
  isDone (Interp.enterScopedClassBody m container name isMod body) = false := by
  intros
  unfold RubyCore.Interp.enterScopedClassBody
  nd_walk

@[simp, ndLem] theorem startFor_notDone :
    ∀ (m : Machine) (targets : List (TargetKind × String)) (body : Expr) (multiple : Bool)
  (collection : Value),
  isDone (Interp.startFor m targets body multiple collection) = false := by
  intros
  unfold RubyCore.Interp.startFor
  nd_walk

@[simp, ndLem] theorem unwindBlockPass_notDone :
    ∀ (m : Machine) (call : ConversionCall) (source : Value) (phase : BlockPassPhase)
  (j : Jump), isDone (Interp.unwindBlockPass m call source phase j) = false := by
  intros
  unfold RubyCore.Interp.unwindBlockPass
  nd_walk

@[simp, ndLem] theorem unwind_notDone :
    ∀ (m : Machine) (j : Jump), isDone (Interp.unwind m j) = false := by
  intros
  unfold RubyCore.Interp.unwind
  nd_walk

@[simp, ndLem] theorem finishStop_notDone :
    ∀ (m : Machine) (owner : Option ObjId) (exc result : Value),
  isDone (Interp.finishStop m owner exc result) = false := by
  intros
  unfold RubyCore.Interp.finishStop
  nd_walk

@[simp, ndLem] theorem finishClassNameError_notDone :
    ∀ (m : Machine) (klass : ObjId) (lead tail : String) (value : Value),
  isDone (Interp.finishClassNameError m klass lead tail value) = false := by
  intros
  unfold RubyCore.Interp.finishClassNameError
  nd_walk

@[simp, ndLem] theorem undefAliasMiss_notDone :
    ∀ (m : Machine) (name : String), isDone (Interp.undefAliasMiss m name) = false := by
  intros
  unfold RubyCore.Interp.undefAliasMiss
  nd_walk

@[simp, ndLem] theorem undefNames_notDone :
    ∀ (m : Machine) (defmod : ObjId) (a : List String),
  isDone (Interp.undefNames m defmod a) = false := by
  intros
  fun_induction RubyCore.Interp.undefNames <;> nd_walk

@[simp, ndLem] theorem stepParamBinding_notDone :
    ∀ (m : Machine) (pending : List (Param × Value)) (body : Expr),
  isDone (Interp.stepParamBinding m pending body) = false := by
  intros
  unfold RubyCore.Interp.stepParamBinding
  nd_walk

@[simp, ndLem] theorem resumeObjectInspect_notDone :
    ∀ (m : Machine) (recv filter : Value) (remaining : List String) (text : String)
  (stringifying : Option Value) (value : Value),
  isDone (Interp.resumeObjectInspect m recv filter remaining text stringifying value) =
    false := by
  intros
  unfold RubyCore.Interp.resumeObjectInspect
  nd_walk

@[simp, ndLem] theorem cpathContainer_notDone :
    ∀ (m : Machine) (base : Value),
  isDoneE (Interp.cpathContainer m base) = false := by
  intros
  unfold RubyCore.Interp.cpathContainer
  nd_walk

/-- `applyKont` at a *non-empty* continuation: every arm either steps, gates, or unwinds —
none of them is the run's own end. -/
@[simp, ndLem] theorem applyKont_notDone (m : Machine) (v : Value) (hne : m.kont ≠ []) :
    isDone (Interp.applyKont m v) = false := by
  rw [Interp.applyKont.eq_def]
  cases hk : m.kont with
  | nil => exact absurd hk hne
  | cons k rest => nd_walk

/-- **The inversion**, and the only thing this file exists for: `.done` is constructed at one
site (`applyKont`'s empty-continuation arm) and `applyKont` is called from one place
(`stepFn`), so a step that ends the run tells you exactly what state it ended in. -/
theorem done_inv (m : Machine) (v : Value) (m' : Machine) (h : Interp.stepFn m = .done v m') :
    m.ctl = .value v ∧ m.kont = [] ∧ m' = m := by
  cases hc : m.ctl with
  | eval e =>
    simp only [Interp.stepFn, hc] at h
    have hnd := evalExpr_notDone (m := m) (e := e)
    rw [h] at hnd
    exact absurd hnd (by simp)
  | jump j =>
    simp only [Interp.stepFn, hc] at h
    have hnd := unwind_notDone (m := m) (j := j)
    rw [h] at hnd
    exact absurd hnd (by simp)
  | send recv site name args blk kw =>
    simp only [Interp.stepFn, hc] at h
    have hnd := invokeQueued_notDone m recv site name args blk kw
    rw [h] at hnd
    exact absurd hnd (by simp)
  | value w =>
    cases hk : m.kont with
    | nil =>
      simp only [Interp.stepFn, hc, Interp.applyKont, hk] at h
      cases h
      -- `cases hk : m.kont` has already rewritten the goal's `m.kont` to `[]`
      exact ⟨rfl, rfl, rfl⟩
    | cons k rest =>
      simp only [Interp.stepFn, hc] at h
      have hnd := applyKont_notDone m w (by rw [hk]; simp)
      rw [h] at hnd
      exact absurd hnd (by simp)

#print axioms evalExpr_notDone
#print axioms unwind_notDone
#print axioms done_inv

end RubyCore.Proof
