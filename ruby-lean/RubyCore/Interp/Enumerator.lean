import RubyCore.Interp.Support

/-! Enumerator's receiver/method descriptor and resumable execution (L280).
    Internal each is an ordinary fresh dispatch; external iteration switches
    control stacks while retaining the shared heap and captured frame store. -/
namespace RubyCore.Interp

def enumBid (bid : String) : Bool :=
  bid.startsWith "Enumerator#" || bid.startsWith "Enumerator::Generator#" ||
    bid.startsWith "Enumerator::Yielder#" ||
    ["Object#enum_for", "Object#to_enum", "Object#__enum_for", "StopIteration#result",
      "Object#__chain_init", "Object#__chain_enums", "Object#binding", "Object#local_variables"].contains bid

def enumQueue (m : Machine) (data : EnumData) (blk : Option Value) : StepResult :=
  .next { m with ctl := .send data.recv .reflective data.method data.args blk data.kw }

def enumNext (m : Machine) (o : ObjId) (peek values : Bool) : StepResult :=
  let st := enumState m o
  if st.caller.isSome then .unsupported "resuming an already running Enumerator" else
  if let some exc := st.finished then enumStop m exc else
  if let some args := st.lookahead then
    let m := setEnumState m o { st with lookahead := if peek then st.lookahead else none }
    let (v, m) := enumPack m args values
    .next { m with ctl := .value v }
  else
    let caller := executionOf m
    let nextState := { st with caller := some caller, peek, values }
    match st.suspended with
    | some fiber =>
      let m := setEnumState m o { nextState with suspended := none, feed := none }
      .next { restoreExecution m fiber with ctl := .value (st.feed.getD .nil) }
    | none =>
      let cl : Closure := { params := [], locals := [], body := .nil, captured := none, home := 0, enumYield := some o }
      let (bo, h) := m.heap.alloc { klass := Boot.procId, payload := .proc cl }
      let owner := m.matchFrameId
      let sharedMatch := match (m.frames.getD owner default).kind with
        | .toplevel => some owner | _ => none
      let root : Frame := { self := .ref o, defmod := Boot.objectId, kind := .toplevel, defVis := .priv, matchAlias := sharedMatch }
      let m := setEnumState { m with heap := h } o nextState
      enumQueue { m with frames := m.frames.push root, stack := [m.frames.size], kont := [.enumFinishK o], currentExc := none, missingReason := .ordinary, activeEnumerator := some o } { recv := .ref o } (some (.ref bo))

def enumArity (m : Machine) (n : Nat) (expected : String) : StepResult :=
  .next (raiseErr m Boot.argumentErrorId s!"wrong number of arguments (given {n}, expected {expected})")

def enumSizeValue (m : Machine) (v : Value) : Except StepResult EnumSize :=
  match v with
  | .nil => .ok .unknown
  | .int _ => .ok (.fixed v)
  | .flt x =>
    if x.isInf && x > 0 then .ok (.fixed v) else
    match Builtins.numIndex m.heap false v with
    | .ok n => .ok (.fixed (.int n))
    | .err c msg => .error (.next (raiseErr m c msg))
    | .gate _ => .error (.unsupported "Enumerator size conversion")
  | .ref o => match (m.heap.get o).payload with
    | .proc _ => .ok (.callback v)
    | _ => .error (.unsupported "Enumerator size through custom to_int")
  | _ =>
    if (lookup m.heap v "to_int").any (fun (_, md) => !md.undefined) ||
        (lookup m.heap v "method_missing").any (fun (_, md) => !md.undefined && md.builtin != some "BasicObject#method_missing") then
      .error (.unsupported "Enumerator size through custom to_int")
    else .error (.next (raiseErr m Boot.typeErrorId
      s!"no implicit conversion of {Builtins.coerceName m.heap v} into Integer"))

def enumInitialize (m : Machine) (o : ObjId) (bid : String) (args : List Value)
    (blk : Option Value) : StepResult :=
  if (m.heap.get o).frozen then raiseFrozen m (.ref o) else
  if (enumState m o).caller.isSome then .unsupported "reinitializing a running Enumerator" else
  let obj := m.heap.get o
  if bid == "Enumerator#initialize" then
    match blk with
    | none => .next (raiseErr m Boot.argumentErrorId "tried to create Proc object without a block")
    | some block =>
      if args.length > 1 then enumArity m args.length "0..1" else
      match enumSizeValue m (args.headD .nil) with
      | .error r => r
      | .ok size =>
        let (go, h) := m.heap.alloc { klass := Boot.generatorId, payload := .generator (some block) }
        let data : EnumData := { recv := .ref go, size }
        let h := h.set o { obj with payload := .enumerator (some data) }
        .next { resetEnumerator { m with heap := h } o with ctl := .value (.ref o) }
  else if bid == "Enumerator::Generator#initialize" then
    let block := match args with | [v] => some v | [] => blk | _ => none
    if args.length > 1 then enumArity m args.length "0..1" else
    match block with
    | none => .next (raiseErr m Boot.localJumpErrorId "no block given")
    | some (.ref p) => match (m.heap.get p).payload with
      | .proc _ => .next { m with heap := m.heap.set o { obj with payload := .generator (some (.ref p)) }, ctl := .value (.ref o) }
      | _ => .unsupported "Generator initializer requires a Proc"
    | _ => .unsupported "Generator initializer requires a Proc"
  else
    if !args.isEmpty then enumArity m args.length "0" else
    match blk with
    | none => .next (raiseErr m Boot.localJumpErrorId "no block given")
    | some block => .next { m with heap := m.heap.set o { obj with payload := .yielder (some block) none }, ctl := .value (.ref o) }

def enumAllocate (m : Machine) (klass : ObjId) : Value × Machine :=
  let payload := if (ancestors m.heap klass).contains Boot.enumeratorId then Payload.enumerator none
    else if (ancestors m.heap klass).contains Boot.generatorId then .generator none else .yielder none none
  let (o, h) := m.heap.alloc { klass, payload }
  (.ref o, { m with heap := h })

def enumMake (m : Machine) (recv : Value) (name : String) (args : List Value := [])
    (size : EnumSize := .unknown) (kw : List (Value × Value) := []) : StepResult :=
  let (v, m) := allocEnumerator m { recv, method := name, args, kw, size }
  .next { m with ctl := .value v }

def callEnumerator (m : Machine) (bid : String) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  if bid == "Object#binding" || bid == "Object#local_variables" then
    if !args.isEmpty || !kw.isEmpty then enumArity m (args.length + if kw.isEmpty then 0 else 1) "0" else
    if m.activeEnumerator.isSome && m.stack.length == 1 then
      if bid == "Object#binding" then
        .next (raiseErr m Boot.runtimeErrorId "Can't create Binding Object on top of Fiber.")
      else let (v, m) := Builtins.allocArr m #[]; .next { m with ctl := .value v }
    else .unsupported "binding/local_variables outside an Enumerator fiber root"
  else if bid == "Object#__chain_init" then
    match recv, args with
    | .ref o, [values] => match Builtins.arrPayload? m.heap values with
      | some xs =>
        if (m.heap.get o).frozen then raiseFrozen m recv else
        .next { m with heap := m.heap.set o { m.heap.get o with payload := .chain xs.toList }, ctl := .value recv }
      | none => .unsupported "Chain internal initializer"
    | _, _ => .unsupported "Chain internal initializer"
  else if bid == "Object#__chain_enums" then
    match recv with
    | .ref o =>
      let initialized := match (m.heap.get o).payload with | .chain _ => true | _ => false
      if (args.headD .nil).identEq (.sym "initialized?") then .next { m with ctl := .value (.bool initialized) }
      else match (m.heap.get o).payload with
      | .chain xs => let (v, m) := Builtins.allocArr m xs.toArray; .next { m with ctl := .value v }
      | _ => .next (raiseErr m Boot.argumentErrorId "uninitialized chain")
    | _ => .unsupported "Chain internal receiver"
  else
  if ["Object#enum_for", "Object#to_enum", "Object#__enum_for"].contains bid then
    let (nameArg, args) : Value × List Value := match args with | [] => (.sym "each", []) | x :: xs => (x, xs)
    match nameArg with
    | .sym name =>
      if bid == "Object#__enum_for" then
        let size := if (args.headD .nil).identEq (.sym "length") then EnumSize.receiverLength
          else if (args.headD .nil).identEq (.sym "receiver_size") then .receiverMethod
          else if (args.headD .nil).identEq (.sym "infinite") then .fixed (.flt (1.0 / 0.0)) else .unknown
        enumMake m recv name args.tail size kw
      else enumMake m recv name args (blk.map EnumSize.callback |>.getD .unknown) kw
    | .ref o => match (m.heap.get o).payload with
      | .str name => enumMake m recv name args (blk.map EnumSize.callback |>.getD .unknown) kw
      | _ => .unsupported "enum_for method-name conversion"
    | _ =>
      if (lookup m.heap nameArg "to_str").any (fun (_, md) => !md.undefined) ||
          (lookup m.heap nameArg "method_missing").any (fun (_, md) => !md.undefined && md.builtin != some "BasicObject#method_missing") then
        .unsupported "enum_for method-name conversion" else
      match Builtins.inspectP m nameArg with
      | .ok text => .next (raiseErr m Boot.typeErrorId s!"{text} is not a symbol nor a string")
      | .error reason => .unsupported reason
  else if bid == "StopIteration#result" then
    if !args.isEmpty || !kw.isEmpty then enumArity m (args.length + if kw.isEmpty then 0 else 1) "0" else
    match recv with
    | .ref o => .next { m with ctl := .value (m.heap.get o).iterationResult }
    | _ => .unsupported "StopIteration result without an exception"
  else match recv with
  | .ref o =>
    if bid.endsWith "#initialize" then
      if !kw.isEmpty then .unsupported "Enumerator initializer keywords" else enumInitialize m o bid args blk
    else match (m.heap.get o).payload with
    | .enumerator none =>
      if bid == "Enumerator#inspect" && args.isEmpty && kw.isEmpty then
        let (v, m) := Builtins.allocStr m s!"#<{className m.heap (m.heap.get o).klass}: uninitialized>"
        .next { m with ctl := .value v }
      else .next (raiseErr m Boot.argumentErrorId "uninitialized enumerator")
    | .enumerator (some data) =>
      let argc := args.length + if kw.isEmpty then 0 else 1
      if bid == "Enumerator#each" then
        -- Additional arguments turn both old and new keyword packets into
        -- positional Hashes. With no additions the original keyword flag stays.
        let (data, m) := if argc == 0 then (data, m) else Id.run do
          let (oldArgs, m) := if data.kw.isEmpty then (data.args, m) else
            let (v, m) := Builtins.allocHsh m data.kw.toArray
            (data.args ++ [v], m)
          let (newArgs, m) := if kw.isEmpty then (args, m) else
            let (v, m) := Builtins.allocHsh m kw.toArray
            (args ++ [v], m)
          return ({ data with args := oldArgs ++ newArgs, kw := [], size := .unknown }, m)
        if blk.isSome then enumQueue m data blk else
        if argc == 0 then .next { m with ctl := .value recv } else
          let (v, m) := allocEnumerator m data (m.heap.get o).klass
          .next { m with ctl := .value v }
      else if bid == "Enumerator#feed" then
        if argc != 1 then enumArity m argc "1" else
        if (m.heap.get o).frozen then raiseFrozen m recv else
        let st := enumState m o
        if st.feed.isSome then .next (raiseErr m Boot.typeErrorId "feed value already set") else
        let (value, m) := if kw.isEmpty then (args.headD .nil, m) else Builtins.allocHsh m kw.toArray
        .next { setEnumState m o { st with feed := some value } with ctl := .value .nil }
      else if bid == "Enumerator#clone" && argc != 0 then .unsupported "Enumerator clone options" else
      if argc != 0 then enumArity m argc "0" else
      if bid == "Enumerator#size" then
        match data.size with
        | .unknown => .next { m with ctl := .value .nil }
        | .fixed v => .next { m with ctl := .value v }
        | .receiverMethod => .next { m with ctl := .send data.recv .reflective "size" [] none [] }
        | .callback (.ref p) => match (m.heap.get p).payload with
          | .proc cl =>
            let (args, m) := if data.kw.isEmpty then (data.args, m) else
              let (v, m) := Builtins.allocHsh m data.kw.toArray
              (data.args ++ [v], m)
            callClosure m cl args none
          | _ => .unsupported "Enumerator size callback without Proc"
        | .callback _ => .unsupported "Enumerator size callback without Proc"
        | .receiverLength => match data.recv with
          | .ref r => match (m.heap.get r).payload with
            | .arr xs => .next { m with ctl := .value (.int xs.size) }
            | .hsh xs => .next { m with ctl := .value (.int xs.size) }
            | _ => .unsupported "Enumerator receiver size"
          | _ => .unsupported "Enumerator receiver size"
      else if bid == "Enumerator#inspect" then
        match Builtins.inspectP m recv with
        | .ok s => let (v, m) := Builtins.allocStr m s; .next { m with ctl := .value v }
        | .error e => .unsupported e
      else if bid == "Enumerator#dup" || bid == "Enumerator#clone" then
        let st := enumState m o
        if (m.heap.get o).eigen.isSome then .unsupported "Enumerator dup/clone with singleton class" else
        if ["initialize_copy", "initialize_dup", "initialize_clone"].any (fun name =>
            (lookup m.heap recv name).any (fun (_, md) => !md.undefined && md.builtin.isNone)) then
          .unsupported "Enumerator copy with user initialization hook" else
        if st.suspended.isSome || st.caller.isSome then
          .next (raiseErr m Boot.typeErrorId "can't copy execution context")
        else
          let (v, m) := Builtins.dupObj m o (bid == "Enumerator#clone")
          .next { m with ctl := .value v }
      else if (m.heap.get o).frozen then raiseFrozen m recv else
      if bid == "Enumerator#rewind" then
        if (enumState m o).caller.isSome then .unsupported "rewinding a running Enumerator" else
        .next { m with ctl := .value data.recv, kont := .blkConvertK (.enumRewind o) data.recv .start :: m.kont }
      else enumNext m o (bid == "Enumerator#peek" || bid == "Enumerator#peek_values")
        (bid == "Enumerator#next_values" || bid == "Enumerator#peek_values")
    | .generator (some (.ref p)) =>
      match (m.heap.get p).payload with
      | .proc cl =>
        if !kw.isEmpty then .unsupported "Generator each keywords" else
        let fid := m.frames.size
        let frame : Frame := { self := recv, defmod := Boot.generatorId, kind := .method, meth := "each", blk, callBlk := blk }
        let (yo, h) := m.heap.alloc { klass := Boot.yielderId, payload := .yielder blk (some fid) }
        let m := { m with heap := h, frames := m.frames.push frame, stack := fid :: m.stack, kont := .frameK fid :: m.kont }
        callClosure m cl (.ref yo :: args) none
      | _ => .unsupported "Generator payload without Proc"
    | .yielder (some (.ref p)) brk =>
      match (m.heap.get p).payload with
      | .proc cl =>
        if !kw.isEmpty then .unsupported "Yielder keywords" else
        if bid == "Enumerator::Yielder#<<" && args.length != 1 then enumArity m args.length "1" else
        let m := if bid == "Enumerator::Yielder#<<" then { m with kont := .newK recv :: m.kont } else m
        callClosure m cl args brk
      | _ => .unsupported "Yielder payload without Proc"
    | .yielder none brk =>
      if brk.isSome then .next (raiseErr m Boot.localJumpErrorId "no block given (yield)")
      else .next (raiseErr m Boot.argumentErrorId "uninitialized yielder")
    | .generator none => .next (raiseErr m Boot.argumentErrorId "uninitialized generator")
    | _ => .unsupported "Enumerator native method without matching payload"
  | _ => .unsupported "Enumerator native method on an immediate"

end RubyCore.Interp
