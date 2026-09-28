import RubyCore.Interp.Construct

/-! Native clone's keyword and initialization protocol (L298). Allocation copies
ivars before the ordinary private hooks; freezing occurs only after normal return. -/
namespace RubyCore.Interp

def nativeCloneBid (bid : String) : Bool :=
  Builtins.cloneBids.contains bid || ["Rational#clone", "Complex#clone", "Enumerator#clone"].contains bid

/-- Keyword errors use Ruby inspection; class-valued diagnostics use to_s. -/
def copyErrorNext (m : Machine) (lead : String) (remaining : List Value)
    (parts : List String) : StepResult :=
  match remaining with
  | [] => .next (raiseErr m Boot.argumentErrorId (lead ++ String.intercalate ", " parts))
  | key :: rest => .next { m with ctl := .send key .reflective "inspect" [] none [], kont := .copyErrorK lead rest parts none :: m.kont }

def finishCopyError (m : Machine) (lead : String) (remaining : List Value)
    (parts : List String) (fallback : Option Value) (value : Value) : StepResult :=
  match Builtins.strPayload? m.heap value with
  | some str =>
    if Builtins.isBinaryStr m.heap value && hasHighByte str then
      .unsupported "copy keyword diagnostic with non-UTF-8 bytes" else
    copyErrorNext m lead remaining (parts ++ [str])
  | none => match fallback with
    | none => .next { m with ctl := .send value .reflective "to_s" [] none [], kont := .copyErrorK lead remaining parts (some value) :: m.kont }
    | some source => match Builtins.run "Object#__any_to_s" source [] m with
      | .ok v m => match Builtins.strPayload? m.heap v with
        | some str => copyErrorNext m lead remaining (parts ++ [str])
        | none => .unsupported "copy diagnostic fallback did not produce a String"
      | result => constructResult result

def copyClassError (m : Machine) (lead : String) (value : Value) : StepResult :=
  let klass := Value.ref (realClassOf m.heap value)
  .next { m with ctl := .send klass .reflective "to_s" [] none [], kont := .copyErrorK lead [] [] (some klass) :: m.kont }

def copyFreezeOption (m : Machine) (kw : List (Value × Value)) : Except StepResult Value :=
  let unknown := (kw.filter (fun p => !p.1.identEq (.sym "freeze"))).map Prod.fst
  if !unknown.isEmpty then .error (copyErrorNext m
    s!"unknown keyword{if unknown.length == 1 then "" else "s"}: " unknown []) else
  let freeze := (kwLookup kw "freeze").getD .nil
  match freeze with
  | .nil | .bool _ => .ok freeze
  | _ => .error (copyClassError m "unexpected value for freeze: " freeze)

def finishNativeClone (m : Machine) (copy original freeze : Value) : StepResult :=
  let frozen := freeze.identEq (.bool true) || (freeze.identEq .nil &&
    match original with | .ref o => (m.heap.get o).frozen | _ => true)
  let m := if frozen then match copy with
    | .ref o =>
      let h := m.heap.set o { m.heap.get o with frozen := true }
      let h := match (h.get o).eigen with
        | some e => h.set e { h.get e with frozen := true }
        | none => h
      { m with heap := h }
    | _ => m
    else m
  .next (withCtl m (.value copy))

def callNativeClone (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  if !args.isEmpty then enumArity m args.length "0" else
  match copyFreezeOption m kw with
  | .error result => result
  | .ok freeze =>
  let immutable := match recv with
    | .ref o => match (m.heap.get o).payload with | .rational .. | .complex .. => true | _ => false
    | _ => true
  if immutable then
    if freeze.identEq (.bool false) then copyClassError m "can't unfreeze " recv
    else .next (withCtl m (.value recv))
  else match recv with
  | .ref o =>
    let src := m.heap.get o
    if src.eigen.isSome then .unsupported "clone of an object with a singleton class" else
    match src.payload with
    | .cls _ => .unsupported "clone of a class/module"
    | .rng _ => .unsupported "clone of a Random (state identity)"
    | _ =>
    let core := match src.payload with | .none | .str _ | .arr _ | .hsh _ | .exc _ => true | _ => false
    if !core then
      -- Preserve already modeled plain copies. Effectful hooks for these native
      -- payloads need their uninitialized allocation/state representation first.
      let defaultHooks := ["initialize_clone", "initialize_copy"].all fun name =>
        (lookup m.heap recv name).any fun (_, md) =>
          !md.undefined && md.builtin == some ("Object#" ++ name)
      if !defaultHooks then .unsupported "native payload clone with custom initialization hooks" else
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
      let kw := if freeze.identEq .nil then [] else [(Value.sym "freeze", freeze)]
      .next { m with heap := h, ctl := .send copy .reflective "initialize_clone" [recv] none kw, kont := .cloneK copy recv freeze :: m.kont }
  | _ => .unsupported "mutable clone without an object"

def callNativeInitializeClone (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  if args.length != 1 then enumArity m args.length "1" else
  match copyFreezeOption m kw with
  | .error result => result
  | .ok _ => .next { m with ctl := .send recv .reflective "initialize_copy" args none [], kont := .newK recv :: m.kont }

/-- Native String/Array/Hash initialize_copy changes the payload, not ivars.
String checks frozen state again after conversion; Array/Hash do not. -/
def finishCoreCopy (m : Machine) (kind : ObjId) (recv source : Value) : StepResult :=
  match recv, source with
  | .ref o, .ref p =>
    let dst := m.heap.get o; let src := m.heap.get p
    if kind == Boot.stringId && dst.frozen then raiseFrozen m recv else
    let dst := if kind == Boot.stringId then { dst with payload := src.payload, binary := src.binary }
      else if kind == Boot.hashId then { dst with payload := src.payload, hashDflt := src.hashDflt }
      else { dst with payload := src.payload }
    .next (withCtl { m with heap := m.heap.set o dst } (.value recv))
  | _, _ => .unsupported "core copy without native objects"

def coreCopyType (kind : ObjId) : String :=
  if kind == Boot.stringId then "String" else if kind == Boot.arrayId then "Array" else "Hash"

def coreCopyPayload (h : Heap) (kind : ObjId) (v : Value) : Bool :=
  if kind == Boot.stringId then (Builtins.strPayload? h v).isSome
  else if kind == Boot.arrayId then (Builtins.arrPayload? h v).isSome
  else (Builtins.hshPayload? h v).isSome

def callCoreCopy (m : Machine) (kind : ObjId) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  if args.length != 1 then enumArity m args.length "1" else
  match recv with
  | .ref o =>
    if (m.heap.get o).frozen then raiseFrozen m recv else
    let source := args.headD .nil
    if recv.identEq source then .next (withCtl m (.value recv)) else
    if kind == Boot.hashId && m.hashIterationActive o then
      .next (raiseErr m Boot.runtimeErrorId "can't replace hash during iteration") else
    if coreCopyPayload m.heap kind source then finishCoreCopy m kind recv source else
    .next (withKont m (.value source) (.blkConvertK (.coreCopy kind recv) source .start))
  | _ => .unsupported "core initialize_copy receiver"

end RubyCore.Interp
