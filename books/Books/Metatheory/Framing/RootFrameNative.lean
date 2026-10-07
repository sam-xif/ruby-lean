import Books.Metatheory.Framing.RootFrameEnumerators
import Books.Metatheory.Framing.RootFrameNativeReflect

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 250000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem finishClassNameError_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (klass : ObjId) (lead tail : String)
    (value : Value) :
    finishClassNameError (pushRootK K m) klass lead tail value = rootFrameR K (finishClassNameError m klass lead tail value) := by
  have hLock := hK.hashLockFree
  unfold finishClassNameError
  root_native_walk K hK

@[rootFrameLem] theorem finishClassInitialize_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (klass : ObjId) (blk : Option Value) :
    finishClassInitialize (pushRootK K m) klass blk = rootFrameR K (finishClassInitialize m klass blk) := by
  have hLock := hK.hashLockFree
  unfold finishClassInitialize
  root_native_walk K hK

def classInitializeParentView (m : Machine) (recv : Value) (klass parent : ObjId)
    (cp : ClassPayload) (blk : Option Value) : StepResult :=
  let parentCp := (m.heap.classPayload? parent).getD default
  let h := m.heap.setClassPayload klass { cp with superclass := some parent, initialized := true, ancestryReady := parentCp.ancestryReady, allocatorUnavailable := parentCp.allocatorUnavailable }
  -- CRuby replaces an allocated class's old metaclass, including its
  -- singleton methods. References to the old metaclass remain live.
  let h := h.set klass { h.get klass with eigen := none }
  let (_, m) := eigenclassOf { m with heap := h } klass
  .next (withKont m (.send (.ref parent) .reflective "inherited" [recv] none []) (.classInitK klass blk))

@[rootFrameLem] theorem classInitializeParentView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (klass parent : ObjId) (cp : ClassPayload) (blk : Option Value) :
    classInitializeParentView (pushRootK K m) recv klass parent cp blk =
      rootFrameR K (classInitializeParentView m recv klass parent cp blk) := by
  unfold classInitializeParentView
  simp only [pushRootK_heap, eigenclassOf_heap_frame, withKont_frame, rootFrameR]

def classInitializeView (m : Machine) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  match recv with
  | .ref klass => match m.heap.classPayload? klass with
    | some cp =>
      if cp.initialized then .next (raiseErr m Boot.typeErrorId "already initialized class")
      else if args.length > 1 then enumArity m args.length "0..1" else
      match inheritableClass m (args.headD (.ref Boot.objectId)) true with
      | .error result => result
      | .ok parent =>
        classInitializeParentView m recv klass parent cp blk
    | none => .unsupported "Class#initialize without a class payload"
  | _ => .unsupported "Class#initialize receiver"


@[rootFrameLem] theorem callClassInitialize_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    callClassInitialize (pushRootK K m) recv args blk kw = rootFrameR K (callClassInitialize m recv args blk kw) := by
  have hLock := hK.hashLockFree
  change classInitializeView (pushRootK K m) recv args blk kw = rootFrameR K (classInitializeView m recv args blk kw)
  unfold classInitializeView
  root_native_walk K hK

@[rootFrameLem] theorem callModuleInitialize_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    callModuleInitialize (pushRootK K m) recv args blk kw = rootFrameR K (callModuleInitialize m recv args blk kw) := by
  have hLock := hK.hashLockFree
  unfold callModuleInitialize
  root_native_walk K hK

@[rootFrameLem] theorem allocateNamespace_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (klass : ObjId) (isModule : Bool) :
    allocateNamespace (pushRootK K m) klass isModule = ((allocateNamespace m klass isModule).1, pushRootK K (allocateNamespace m klass isModule).2) := by
  have hLock := hK.hashLockFree
  unfold allocateNamespace
  root_native_walk K hK

@[rootFrameLem] theorem legacyConstruct_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (klass : ObjId)
    (args : List Value) (_blk : Option Value) (kw : List (Value × Value)) :
    legacyConstruct (pushRootK K m) recv klass args _blk kw = rootFrameR K (legacyConstruct m recv klass args _blk kw) := by
  have hLock := hK.hashLockFree
  unfold legacyConstruct
  root_native_walk K hK

def procConstructView (m : Machine) (klass o : ObjId) (cl : Closure)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let (inst, m) := if (m.heap.get o).klass == klass then (Value.ref o, m) else
    let (o, h) := m.heap.alloc {klass, payload := .proc cl}
    (Value.ref o, {m with heap := h})
  initializeInstance m inst args blk kw

@[rootFrameLem] theorem procConstructView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (klass o : ObjId) (cl : Closure)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    procConstructView (pushRootK K m) klass o cl args blk kw =
      rootFrameR K (procConstructView m klass o cl args blk kw) := by
  unfold procConstructView
  by_cases hc : (m.heap.get o).klass == klass <;>
    simp only [pushRootK_heap, hc, if_true, if_false] <;> root_native_walk K hK

def coreConstructView (m : Machine) (klass : ObjId) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let payload := match Builtins.allocatableCore m.heap klass with
    | some core => Builtins.emptyCorePayload core
    | none => Payload.none
  let (o, h) := m.heap.alloc { klass, payload }
  initializeInstance { m with heap := h } (.ref o) args blk kw

@[rootFrameLem] theorem coreConstructView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (klass : ObjId) (args : List Value) (blk : Option Value)
    (kw : List (Value × Value)) :
    coreConstructView (pushRootK K m) klass args blk kw =
      rootFrameR K (coreConstructView m klass args blk kw) := by
  unfold coreConstructView
  simp only [pushRootK_heap]
  exact initializeInstance_frame K hK {m with heap := (m.heap.alloc
    {klass, payload := match allocatableCore m.heap klass with
      | some core => emptyCorePayload core | none => Payload.none}).2}
    (.ref m.heap.objs.size) args blk kw

def constructView (m : Machine) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  match recv with
  | .ref klass => match m.heap.classPayload? klass with
    | none => .unsupported "new on a non-class"
    | some cp =>
      if cp.isModule then .unsupported "new on a module" else
      if cp.attached.isSome then .next (raiseErr m Boot.typeErrorId "can't create instance of singleton class") else
      if !cp.initialized then .next (raiseErr m Boot.typeErrorId "can't instantiate uninitialized class") else
      if cp.allocatorUnavailable then classNameTypeError m klass "allocator undefined for " "" else
      let chain := ancestors m.heap klass
      if chain.contains Boot.moduleId then
        let (inst, m) := allocateNamespace m klass (klass != Boot.classId)
        initializeInstance m inst args blk kw
      else if chain.any ([Boot.enumeratorId, Boot.generatorId, Boot.yielderId].contains ·) then
        let (inst, m) := enumAllocate m klass
        initializeInstance m inst args blk kw
      else if chain.contains Boot.procId then
        match blk with
        | none => .next (raiseErr m Boot.argumentErrorId "tried to create Proc object without a block")
        | some (.ref o) => match (m.heap.get o).payload with
          | .proc cl =>
            procConstructView m klass o cl args blk kw
          | _ => .unsupported "Proc constructor block is not a Proc"
        | some _ => .unsupported "Proc constructor block is not a Proc"
      else if [Boot.randomId, Boot.regexpId].contains klass then
        legacyConstruct m recv klass args blk kw
      else if chain.any ([Boot.randomId, Boot.regexpId,
          Boot.rangeId].contains ·) then
        .unsupported "constructor for an unmodeled native payload subclass"
      else if chain.any ([Boot.integerId, Boot.floatId, Boot.symbolId, Boot.rationalId,
          Boot.complexId, Boot.nilClassId, Boot.trueClassId, Boot.falseClassId].contains ·) then
        .next (raiseErr m Boot.typeErrorId s!"allocator undefined for {className m.heap klass}")
      else
        coreConstructView m klass args blk kw
  | _ => .unsupported "new on a non-class"


@[rootFrameLem] theorem callConstruct_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    callConstruct (pushRootK K m) recv args blk kw = rootFrameR K (callConstruct m recv args blk kw) := by
  have hLock := hK.hashLockFree
  change constructView (pushRootK K m) recv args blk kw = rootFrameR K (constructView m recv args blk kw)
  unfold constructView
  simp only [pushRootK_heap]
  repeat' (first
    | with_reducible rfl
    | root_split
    | root_progress (simp (disch := assumption) only [rootFrameLem, Option.map_some, Option.map_none])
    | root_back K hK
    | root_progress (simp_all only [rootFrameLem]))

@[rootFrameLem] theorem callAllocate_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) :
    callAllocate (pushRootK K m) recv args kw = rootFrameR K (callAllocate m recv args kw) := by
  have hLock := hK.hashLockFree
  unfold callAllocate
  root_native_walk K hK

@[rootFrameLem] theorem raiseString_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (message : Value) :
    raiseString (pushRootK K m) message = rootFrameR K (raiseString m message) := by
  have hLock := hK.hashLockFree
  unfold raiseString
  root_native_walk K hK

@[rootFrameLem] theorem callExceptionMessage_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) :
    callExceptionMessage (pushRootK K m) recv args kw = rootFrameR K (callExceptionMessage m recv args kw) := by
  have hLock := hK.hashLockFree
  unfold callExceptionMessage
  root_native_walk K hK

@[rootFrameLem] theorem callUncaughtMessage_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) :
    callUncaughtMessage (pushRootK K m) recv args kw = rootFrameR K (callUncaughtMessage m recv args kw) := by
  have hLock := hK.hashLockFree
  unfold callUncaughtMessage
  root_native_walk K hK

@[rootFrameLem] theorem finishUncaughtInspect_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (source : Option Value) (v : Value) :
    finishUncaughtInspect (pushRootK K m) source v = rootFrameR K (finishUncaughtInspect m source v) := by
  have hLock := hK.hashLockFree
  unfold finishUncaughtInspect
  root_native_walk K hK

@[rootFrameLem] theorem callRaise_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (args : List Value) (kw : List (Value × Value)) :
    callRaise (pushRootK K m) args kw = rootFrameR K (callRaise m args kw) := by
  have hLock := hK.hashLockFree
  unfold callRaise
  root_native_walk K hK

@[rootFrameLem] theorem callExceptionCopy_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) :
    callExceptionCopy (pushRootK K m) recv args kw = rootFrameR K (callExceptionCopy m recv args kw) := by
  have hLock := hK.hashLockFree
  unfold callExceptionCopy
  root_native_walk K hK

@[rootFrameLem] theorem arrayInitNext_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : ObjId) (block : Value) (index size : Nat)
    (v : Value) :
    arrayInitNext (pushRootK K m) recv block index size v = rootFrameR K (arrayInitNext m recv block index size v) := by
  have hLock := hK.hashLockFree
  unfold arrayInitNext
  root_native_walk K hK

def hashDefaultValidView (m : Machine) (block : Value) : Except StepResult Unit := do
  match procClosure? m block with
  | some cl =>
    if cl.lam then
      match classifySimple cl.params with
      | none => .error (.unsupported "Hash default lambda with complex parameters")
      | some ps =>
        let required := ps.pre.length + ps.post.length
        if required > 2 || (ps.rest?.isNone && required != 2) then
          .error (.next (raiseErr m Boot.typeErrorId s!"default_proc takes two arguments (2 for {required})"))
        else .ok ()
    else .ok ()
  | none => .error (.unsupported "Hash initializer block is not a Proc")

@[rootFrameLem] theorem hashDefaultValidView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (block : Value) :
    hashDefaultValidView (pushRootK K m) block =
      (hashDefaultValidView m block).mapError (rootFrameR K) := by
  unfold hashDefaultValidView
  root_native_walk K hK
  all_goals rfl

def coreInitializeView (m : Machine) (bid : String) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  match recv, blk with
  | .ref o, some block =>
    if bid == "Hash#initialize" then
      if args.length > 1 then enumArity m args.length "0..1" else
      if (m.heap.get o).frozen then raiseFrozen m recv else
      if !args.isEmpty then enumArity m args.length "0" else
      let valid := hashDefaultValidView m block
      match valid with
      | .error result => result
      | .ok _ =>
      match block with
      | .ref bo =>
        let h := m.heap.set o { m.heap.get o with hashDflt := some (.prc bo) }
        .next (withCtl { m with heap := h } (.value recv))
      | _ => .unsupported "Hash initializer block is not a Proc"
    else if bid == "Array#initialize" && !args.isEmpty then
      match args with
      | .int size :: rest =>
        if (m.heap.get o).frozen then raiseFrozen m recv else
        if rest.length > 1 then enumArity m args.length "0..2" else
        if size < 0 then .next (raiseErr m Boot.argumentErrorId "negative array size") else
        let h := m.heap.set o { m.heap.get o with payload := .arr #[] }
        arrayInitYield { m with heap := h } o block 0 size.toNat
      | _ => constructResult (Builtins.run bid recv args m)
    else constructResult (Builtins.run bid recv args m)
  | _, _ => constructResult (Builtins.run bid recv args m)


@[rootFrameLem] theorem callCoreInitialize_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (bid : String) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    callCoreInitialize (pushRootK K m) bid recv args blk kw = rootFrameR K (callCoreInitialize m bid recv args blk kw) := by
  have hLock := hK.hashLockFree
  change coreInitializeView (pushRootK K m) bid recv args blk kw = rootFrameR K (coreInitializeView m bid recv args blk kw)
  unfold coreInitializeView
  root_native_walk K hK


#print axioms RubyCore.Proof.Root.callConstruct_frame
#print axioms RubyCore.Proof.Root.callCoreInitialize_frame
end RubyCore.Proof.Root
