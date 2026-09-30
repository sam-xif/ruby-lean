import RubyCore.Proof.RootFrameDispatch

/-! Root-execution framing for native copy and library calls. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem rootFrameR_ite (K : List Kont) (p : Prop) [Decidable p]
    (a b : StepResult) : rootFrameR K (if p then a else b) =
      if p then rootFrameR K a else rootFrameR K b := by
  by_cases h : p <;> simp [h]

attribute [local rootFrameLem] hashIterationActive_rootFrame

@[rootFrameLem] theorem enumState_suspended_isSome_frame (K : List Kont) (m : Machine) (o : ObjId) :
    (enumState (pushRootK K m) o).suspended.isSome = (enumState m o).suspended.isSome := by
  simp only [enumState_rootFrame, frameEnumState, Option.isSome_map]

@[rootFrameLem] theorem enumState_caller_isSome_frame (K : List Kont) (m : Machine) (o : ObjId) :
    (enumState (pushRootK K m) o).caller.isSome = (enumState m o).caller.isSome := by
  simp only [enumState_rootFrame, frameEnumState, Option.isSome_map]


@[rootFrameLem] theorem finishCopyError_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (lead : String) (remaining : List Value)
    (parts : List String) (fallback : Option Value) (value : Value) :
    finishCopyError (pushRootK K m) lead remaining parts fallback value = rootFrameR K (finishCopyError m lead remaining parts fallback value) := by
  have hLock := hK.hashLockFree
  unfold finishCopyError
  cases hs : strPayload? m.heap value with
  | some str => simp only [rootFrameLem, hs]; root_dispatch_walk K hK
  | none =>
    cases fallback with
    | none => simp only [rootFrameLem, hs]; root_dispatch_walk K hK
    | some source =>
      cases hr : Builtins.run "Object#__any_to_s" source [] m <;>
        simp (disch := assumption) only [rootFrameLem, hs, hr, bRootPush, constructResult] <;>
        root_dispatch_walk K hK

@[rootFrameLem] theorem copyFreezeOption_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (kw : List (Value × Value)) :
    copyFreezeOption (pushRootK K m) kw = (copyFreezeOption m kw).mapError (rootFrameR K) := by
  have hLock := hK.hashLockFree
  unfold copyFreezeOption
  root_dispatch_walk K hK

def nativeCopyView (m : Machine) (recv : Value) (clone : Bool) (freeze : Value) : StepResult :=
  let immutable := match recv with
    | .ref o => match (m.heap.get o).payload with | .rational .. | .complex .. => true | _ => false
    | _ => true
  if immutable then
    if clone && freeze.identEq (.bool false) then copyClassError m "can't unfreeze " recv
    else .next (withCtl m (.value recv))
  else match recv with
  | .ref o =>
    let src := m.heap.get o
    if clone && src.eigen.isSome then .unsupported "clone of an object with a singleton class" else
    match src.payload with
    | .cls _ => .unsupported "dup/clone of a class/module"
    | .rng _ => .unsupported "dup/clone of a Random (state identity)"
    | _ =>
    let core := match src.payload with | .none | .str _ | .arr _ | .hsh _ | .exc _ => true | _ => false
    if !core then
      -- Preserve already modeled plain copies. Effectful hooks for these native
      -- payloads need their uninitialized allocation/state representation first.
      let hook := if clone then "initialize_clone" else "initialize_dup"
      let defaultHooks := [hook, "initialize_copy"].all fun name =>
        (methodOn m.heap src.klass name).any fun (_, md) =>
          !md.undefined && md.builtin == some ("Object#" ++ name)
      if !defaultHooks then .unsupported "native payload copy with custom initialization hooks" else
      if let .enumerator _ := src.payload then
        let st := enumState m o
        if st.suspended.isSome || st.caller.isSome then
          .next (raiseErr m Boot.typeErrorId "can't copy execution context")
        else
          let (copy, m) := Builtins.dupObj m o false
          finishNativeClone m copy recv freeze
      else
        let (copy, m) := Builtins.dupObj m o false
        finishNativeClone m copy recv freeze
    else
      let cp := (m.heap.classPayload? src.klass).getD default
      if cp.allocatorUnavailable then classNameTypeError m src.klass "allocator undefined for " "" else
      let payload := match src.payload with
        | .str _ => Payload.str ""
        | .arr _ => .arr #[]
        | .hsh _ => .hsh #[]
        | p => p
      let binary := match src.payload with | .str _ => true | _ => src.binary
      let (copy, h) := m.heap.alloc { klass := src.klass, payload, binary, ivars := src.ivars, iterationResult := src.iterationResult, throwTag := src.throwTag, throwValue := src.throwValue }
      let copy := Value.ref copy
      let kw := if !clone || freeze.identEq .nil then [] else [(Value.sym "freeze", freeze)]
      let hook := if clone then "initialize_clone" else "initialize_dup"
      let kont := if clone then Kont.cloneK copy recv freeze else Kont.newK copy
      .next (withKont { m with heap := h } (.send copy .reflective hook [recv] none kw) kont)
  | _ => .unsupported "mutable copy without an object"

@[rootFrameLem] theorem beginNativeCopy_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (clone : Bool) (freeze : Value) :
    beginNativeCopy (pushRootK K m) recv clone freeze = rootFrameR K (beginNativeCopy m recv clone freeze) := by
  have hLock := hK.hashLockFree
  change nativeCopyView (pushRootK K m) recv clone freeze = rootFrameR K (nativeCopyView m recv clone freeze)
  unfold nativeCopyView
  cases recv <;> root_dispatch_walk K hK


@[rootFrameLem] theorem callNativeClone_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) :
    callNativeClone (pushRootK K m) recv args kw = rootFrameR K (callNativeClone m recv args kw) := by
  have hLock := hK.hashLockFree
  unfold callNativeClone
  cases hf : copyFreezeOption m kw <;> simp only [rootFrameLem, hf, Except.mapError]
  all_goals
  root_dispatch_walk K hK

@[rootFrameLem] theorem callNativeDup_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) :
    callNativeDup (pushRootK K m) recv args kw = rootFrameR K (callNativeDup m recv args kw) := by
  have hLock := hK.hashLockFree
  unfold callNativeDup
  root_dispatch_walk K hK

@[rootFrameLem] theorem callNativeInitializeDup_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) :
    callNativeInitializeDup (pushRootK K m) recv args kw = rootFrameR K (callNativeInitializeDup m recv args kw) := by
  have hLock := hK.hashLockFree
  unfold callNativeInitializeDup
  root_dispatch_walk K hK
  cases he : (appendKwHash m args kw).2.activeEnumerator <;>
    simp [pushRootK, he]

@[rootFrameLem] theorem callNativeInitializeClone_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) :
    callNativeInitializeClone (pushRootK K m) recv args kw = rootFrameR K (callNativeInitializeClone m recv args kw) := by
  have hLock := hK.hashLockFree
  unfold callNativeInitializeClone
  cases hf : copyFreezeOption m kw <;> simp only [rootFrameLem, hf, Except.mapError]
  all_goals
  root_dispatch_walk K hK

@[rootFrameLem] theorem finishCoreCopy_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (kind : ObjId) (recv source : Value) :
    finishCoreCopy (pushRootK K m) kind recv source = rootFrameR K (finishCoreCopy m kind recv source) := by
  have hLock := hK.hashLockFree
  unfold finishCoreCopy
  root_dispatch_walk K hK

@[rootFrameLem] theorem callCoreCopy_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (kind : ObjId) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) :
    callCoreCopy (pushRootK K m) kind recv args kw = rootFrameR K (callCoreCopy m kind recv args kw) := by
  have hLock := hK.hashLockFree
  unfold callCoreCopy
  root_dispatch_walk K hK

@[rootFrameLem] theorem callRequire_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (bid : String) (args : List Value)
    (kw : List (Value × Value)) :
    callRequire (pushRootK K m) bid args kw = rootFrameR K (callRequire m bid args kw) := by
  have hLock := hK.hashLockFree
  unfold callRequire
  root_dispatch_walk K hK

def forwardableView (m : Machine) (args : List Value) : StepResult :=
  if !m.currentFrame.libraryOrigin then .unsupported "internal Forwardable compiler" else
  if ["eval", "caller_locations"].any (fun name =>
      (lookup m.heap m.currentFrame.self name).any (fun (_, md) => md.builtin.isNone)) ||
      (lookup m.heap (.sym "") "to_s").any (fun (_, md) => md.builtin.isNone) then
    .unsupported "Forwardable source generation with user eval/location/Symbol conversion overrides" else
  match args with
  | [accessor, method, aliasName, isMethod, checked] =>
    if checked.truthy && m.stack.length <= 2 then
      .unsupported "Forwardable generator without a source caller location" else
    match symOrStr m accessor, symOrStr m method, symOrStr m aliasName with
    | some acc, some meth, some ali =>
      if !forwardableMethodName meth || !forwardableMethodName ali then
        .unsupported "Forwardable generated method syntax" else
      match forwardableAccessor acc isMethod.truthy with
      | none => .unsupported "Forwardable accessor expression needs general source compilation"
      | some access =>
        let target := Expr.var .lvar "_"
        let call := Expr.send (some target) meth [.fwd] none
        let body := if checked.truthy then
          Expr.seq [.vasgn .lvar "_" access,
            .if' (.defined (.send (some target) meth [] none)) call
              (some (.send none "__unsupported__" [.str "Forwardable warning path needs source locations and Kernel.warn"] none))]
          else Expr.send (some access) "__send__" [.sym meth, .fwd] none
        -- The ordinary frame now keeps the helper's lexical definee separately
        -- from its singleton-method owner. *_eval can rebind it when called.
        let (value, m) := reifyBlock m [] [] (.def' ali [.fwd] body) false
        .next (withCtl m (.value value))
    | _, _, _ => .unsupported "Forwardable source compilation with non-name values"
  | _ => .unsupported "internal Forwardable compiler arity"

@[rootFrameLem] theorem compileForwardable_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (args : List Value) :
    compileForwardable (pushRootK K m) args = rootFrameR K (compileForwardable m args) := by
  have hLock := hK.hashLockFree
  change forwardableView (pushRootK K m) args = rootFrameR K (forwardableView m args)
  unfold forwardableView
  root_dispatch_walk K hK
  all_goals try simp_all (disch := assumption) only [rootFrameLem, Bool.and_eq_true, decide_eq_true_eq]

#print axioms beginNativeCopy_frame
#print axioms compileForwardable_frame
end RubyCore.Proof.Root
