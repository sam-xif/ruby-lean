import RubyCore.Interp.Reflect

/-! Native construction is selected by the resolved method, after lookup and
visibility. Allocation does not send `allocate`; initialization is an ordinary
private send, including undef/method_missing, aliases and block forwarding. -/
namespace RubyCore.Interp

def constructResult : BRes → StepResult
  | .ok v m => .next (withCtl m (.value v))
  | .err cls msg m => .next (raiseErr m cls msg)
  | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
  | .frozen recv m => raiseFrozen m recv
  | .unsupported reason => .unsupported reason

def initializeInstance (m : Machine) (inst : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  .next { m with ctl := .send inst .reflective "initialize" args blk kw, kont := .newK inst :: m.kont }

def finishClassNameError (m : Machine) (klass : ObjId) (lead tail : String)
    (value : Value) : StepResult :=
  let finish (m : Machine) (value : Value) : StepResult :=
    match Builtins.strPayload? m.heap value with
    | none => .unsupported "native class-name diagnostic did not produce a String"
    | some name =>
      if Builtins.isBinaryStr m.heap value && hasHighByte name then
        .unsupported "native class-name diagnostic with non-UTF-8 bytes"
      else .next (raiseErr m Boot.typeErrorId (lead ++ name ++ tail))
  if (Builtins.strPayload? m.heap value).isSome then finish m value else
  match Builtins.run "Object#__any_to_s" (.ref klass) [] m with
  | .ok value m => finish m value
  | result => constructResult result

/-- Module initialization executes its block as module_exec and discards only
    its normal result. Break/return/raise keep the ordinary block boundaries. -/
def initializeModuleBlock (m : Machine) (klass : ObjId) (blk : Option Value)
    (result : Value) : StepResult :=
  match blk with
  | none => .next (withCtl m (.value result))
  | some block => match procClosure? m block with
    | some cl => callClosure { m with kont := .newK result :: m.kont }
        cl [.ref klass] none (some (.ref klass)) (some klass)
    | none => .unsupported "class/module initializer block is not a Proc"

def finishClassInitialize (m : Machine) (klass : ObjId) (blk : Option Value) : StepResult :=
  initializeModuleBlock m klass blk (.ref klass)

def callClassInitialize (m : Machine) (recv : Value) (args : List Value)
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
        let parentCp := (m.heap.classPayload? parent).getD default
        let h := m.heap.setClassPayload klass { cp with superclass := some parent, initialized := true, ancestryReady := parentCp.ancestryReady, allocatorUnavailable := parentCp.allocatorUnavailable }
        -- CRuby replaces an allocated class's old metaclass, including its
        -- singleton methods. References to the old metaclass remain live.
        let h := h.set klass { h.get klass with eigen := none }
        let (_, m) := eigenclassOf { m with heap := h } klass
        .next { m with ctl := .send (.ref parent) .reflective "inherited" [recv] none [], kont := .classInitK klass blk :: m.kont }
    | none => .unsupported "Class#initialize without a class payload"
  | _ => .unsupported "Class#initialize receiver"

def callModuleInitialize (m : Machine) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  if !args.isEmpty then enumArity m args.length "0" else
  match recv with
  | .ref klass => initializeModuleBlock m klass blk .nil
  | _ => .unsupported "Module#initialize receiver"

def allocateNamespace (m : Machine) (klass : ObjId) (isModule : Bool) : Value × Machine :=
  let (o, h) := m.heap.alloc { klass, payload := .cls { superclass := none, name := "", isModule, initialized := isModule, ancestryReady := isModule, allocatorUnavailable := !isModule } }
  (.ref o, { m with heap := h })

/-- Random and Regexp retain argument-dependent allocation until their empty
    native payloads are modeled. Class/Module use the ordinary initialize path. -/
def legacyConstruct (m : Machine) (recv : Value) (klass : ObjId)
    (args : List Value) (_blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  if (methodOn m.heap klass "initialize").any (fun (_, md) =>
      md.undefined || md.builtin != some "BasicObject#initialize") then
    .unsupported "native constructor with a replaced initializer" else
  let (args, m) := appendKwHash m args kw
  constructResult (Builtins.newImpl m recv args)

def callConstruct (m : Machine) (recv : Value) (args : List Value)
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
            let (inst, m) := if (m.heap.get o).klass == klass then (Value.ref o, m) else
              let (o, h) := m.heap.alloc { klass, payload := .proc cl }
              (Value.ref o, { m with heap := h })
            initializeInstance m inst args blk kw
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
        let payload := match Builtins.allocatableCore m.heap klass with
          | some core => Builtins.emptyCorePayload core
          | none => Payload.none
        let (o, h) := m.heap.alloc { klass, payload }
        initializeInstance { m with heap := h } (.ref o) args blk kw
  | _ => .unsupported "new on a non-class"

def callAllocate (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  if !args.isEmpty then enumArity m args.length "0" else
  match recv with
  | .ref klass =>
    match m.heap.classPayload? klass with
    | none => constructResult (Builtins.run "Class#allocate" recv args m)
    | some cp =>
    if cp.attached.isSome then .next (raiseErr m Boot.typeErrorId "can't create instance of singleton class") else
    if !cp.initialized then .next (raiseErr m Boot.typeErrorId "can't instantiate uninitialized class") else
    if cp.allocatorUnavailable then classNameTypeError m klass "allocator undefined for " "" else
    if (ancestors m.heap klass).contains Boot.moduleId then
      let (inst, m) := allocateNamespace m klass (klass != Boot.classId)
      .next (withCtl m (.value inst))
    else if (ancestors m.heap klass).any ([Boot.enumeratorId, Boot.generatorId, Boot.yielderId].contains ·) then
      let (v, m) := enumAllocate m klass
      .next (withCtl m (.value v))
    else constructResult (Builtins.run "Class#allocate" recv args m)
  | _ => constructResult (Builtins.run "Class#allocate" recv args m)

def raiseString (m : Machine) (message : Value) : StepResult :=
  callConstruct { m with kont := .raiseValueK :: m.kont }
    (.ref Boot.runtimeErrorId) [message] none []

def callExceptionMessage (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  if !args.isEmpty then enumArity m args.length "0" else
  match recv with
  | .ref o => match (m.heap.get o).payload with
    | .exc message =>
      if message.identEq .nil then
        let (v, m) := Builtins.allocStr m (className m.heap (m.heap.get o).klass)
        .next (withCtl m (.value v))
      else if (Builtins.strPayload? m.heap message).isSome then
        .next (withCtl m (.value message))
      else .next (withKont m (.value message) (.blkConvertK (.exceptionString false) message .start))
    | _ => .unsupported "Exception message without an exception payload"
  | _ => .unsupported "Exception message on a non-object"

/-- The native default throw format inspects the live tag at message time.
    Other printf formats remain outside the current String formatter fragment. -/
def callUncaughtMessage (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  if !args.isEmpty then enumArity m args.length "0" else
  match recv with
  | .ref o => match (m.heap.get o).payload with
    | .exc message => match Builtins.strPayload? m.heap message with
      | some str =>
        if str == "uncaught throw %p" then
          .next { m with ctl := .send (m.heap.get o).throwTag .reflective "inspect" [] none [], kont := .uncaughtInspectK none :: m.kont }
        else if !str.contains '%' then
          let (v, m) := Builtins.allocStrEnc m str (Builtins.isBinaryStr m.heap message)
          .next (withCtl m (.value v))
        else .unsupported "UncaughtThrowError custom printf format"
      | none => .unsupported "UncaughtThrowError format String conversion"
    | _ => .unsupported "UncaughtThrowError without exception payload"
  | _ => .unsupported "UncaughtThrowError receiver"

def finishUncaughtInspect (m : Machine) (source : Option Value) (v : Value) : StepResult :=
  match Builtins.strPayload? m.heap v with
  | some str =>
    if Builtins.isBinaryStr m.heap v && hasHighByte str then
      .unsupported "UncaughtThrowError tag containing non-UTF-8 bytes" else
    let (v, m) := Builtins.allocStr m ("uncaught throw " ++ str)
    .next (withCtl m (.value v))
  | none => match source with
    | none => .next { m with ctl := .send v .reflective "to_s" [] none [], kont := .uncaughtInspectK (some v) :: m.kont }
    | some source => match Builtins.run "Object#__any_to_s" source [] m with
      | .ok repr m => match Builtins.strPayload? m.heap repr with
        | some str =>
          let (v, m) := Builtins.allocStr m ("uncaught throw " ++ str)
          .next (withCtl m (.value v))
        | none => .unsupported "UncaughtThrowError generic String rendering"
      | result => constructResult result

def callRaise (m : Machine) (args : List Value) (kw : List (Value × Value)) : StepResult :=
  if !kw.isEmpty then .unsupported "raise keyword/cause protocol" else
  match args with
  | [] => match m.currentExc with
    | some exc => .next (withCtl m (.jump (.raiseJ exc)))
    | none =>
      let (message, m) := Builtins.allocStr m ""
      raiseString m message
  | [source] =>
    if (Builtins.strPayload? m.heap source).isSome then raiseString m source else
    .next (withKont m (.value source) (.blkConvertK .raiseString source .start))
  | [source, message] =>
    .next (withKont m (.value source) (.blkConvertK (.raiseException [message]) source .start))
  | _ => .unsupported "raise backtrace/arity protocol"

/-- Exception#exception copies the receiver and replaces its raw message,
    without dispatching initialize. Class-side exception uses callConstruct. -/
def callExceptionCopy (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  if args.length > 1 then enumArity m args.length "0..1" else
  if args.isEmpty || (args.headD .nil).identEq recv then
    .next (withCtl m (.value recv)) else
  match recv with
  | .ref o =>
    if (m.heap.get o).eigen.isSome then .unsupported "Exception copy with singleton methods" else
    let (copy, m) := Builtins.dupObj m o false
    .next { m with ctl := .send copy .reflective "initialize_clone" [recv] none [], kont := .exceptionCopyK copy (args.headD .nil) recv :: m.kont }
  | _ => .unsupported "Exception copy on a non-object"

def callInitializeClone (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  if !kw.isEmpty then .unsupported "initialize_clone freeze keyword" else
  if args.length != 1 then enumArity m args.length "1" else
  .next { m with ctl := .send recv .reflective "initialize_copy" args none [], kont := .newK recv :: m.kont }

def arrayInitYield (m : Machine) (recv : ObjId) (block : Value) (index size : Nat) : StepResult :=
  if index >= size then .next (withCtl m (.value (.ref recv))) else
  match procClosure? m block with
  | some cl => callClosure { m with kont := .arrayInitK recv block index size :: m.kont }
      cl [.int index] none
  | none => .unsupported "Array initializer block is not a Proc"

def arrayInitNext (m : Machine) (recv : ObjId) (block : Value) (index size : Nat)
    (v : Value) : StepResult :=
  if (m.heap.get recv).frozen then raiseFrozen m (.ref recv) else
  match (m.heap.get recv).payload with
  | .arr xs =>
    let xs := if index < xs.size then xs else xs ++ Array.replicate (index + 1 - xs.size) .nil
    let h := m.heap.set recv { m.heap.get recv with payload := .arr (xs.set! index v) }
    arrayInitYield { m with heap := h } recv block (index + 1) size
  | _ => .unsupported "Array initializer receiver has no Array payload"

def callCoreInitialize (m : Machine) (bid : String) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  match recv, blk with
  | .ref o, some block =>
    if bid == "Hash#initialize" then
      if args.length > 1 then enumArity m args.length "0..1" else
      if (m.heap.get o).frozen then raiseFrozen m recv else
      if !args.isEmpty then enumArity m args.length "0" else
      let valid : Except StepResult Unit := do
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

end RubyCore.Interp
