import Books.Metatheory.Framing.RootFrameNativeSupport

/-! Framing reflection, native constructors, and library callbacks. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 600000
namespace RubyCore.Proof.Root
open Builtins Interp

def enumEachArgsView (m : Machine) (data : EnumData) (args : List Value)
    (kw : List (Value × Value)) : EnumData × Machine :=
  let argc := args.length + if kw.isEmpty then 0 else 1
   if argc == 0 then (data, m) else Id.run do
          let (oldArgs, m) := if data.kw.isEmpty then (data.args, m) else
            let (v, m) := Builtins.allocHsh m data.kw.toArray
            (data.args ++ [v], m)
          let (newArgs, m) := if kw.isEmpty then (args, m) else
            let (v, m) := Builtins.allocHsh m kw.toArray
            (args ++ [v], m)
          return ({ data with args := oldArgs ++ newArgs, kw := [], size := .unknown }, m)

@[rootFrameLem] theorem enumEachArgsView_frame (K : List Kont) (m : Machine)
    (data : EnumData) (args : List Value) (kw : List (Value × Value)) :
    enumEachArgsView (pushRootK K m) data args kw =
      ((enumEachArgsView m data args kw).1, pushRootK K (enumEachArgsView m data args kw).2) := by
  unfold enumEachArgsView
  dsimp only
  root_split
  · rfl
  · cases hd : data.kw.isEmpty <;> cases hk : kw.isEmpty <;>
      simp only [hd, hk, Bool.false_eq_true, if_false, if_true,
        rootFrameLem, Id.run, bind, pure]


@[rootFrameLem] theorem enumFeedValue_frame (K : List Kont) (m : Machine) (o : ObjId) (v : Value) :
    withCtl (setEnumState (pushRootK K m) o { enumState (pushRootK K m) o with feed := some v }) (.value .nil) =
      pushRootK K (withCtl (setEnumState m o { enumState m o with feed := some v }) (.value .nil)) := by
  rw [enumState_feed_update_frame, withCtl_frame]

def enumEachView (m : Machine) (o : ObjId) (data : EnumData) (recv : Value)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let argc := args.length + if kw.isEmpty then 0 else 1
  let (data, m) := enumEachArgsView m data args kw
  if blk.isSome then enumQueue m data blk else
  if argc == 0 then .next (withCtl m (.value recv)) else
    let (v, m) := allocEnumerator m data (m.heap.get o).klass
    .next (withCtl m (.value v))

@[rootFrameLem] theorem enumEachView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o : ObjId) (data : EnumData) (recv : Value)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    enumEachView (pushRootK K m) o data recv args blk kw =
      rootFrameR K (enumEachView m o data recv args blk kw) := by
  unfold enumEachView
  root_native_walk K hK

def enumDataView (m : Machine) (o : ObjId) (data : EnumData) (bid : String) (recv : Value)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let argc := args.length + if kw.isEmpty then 0 else 1
  if bid == "Enumerator#each" then
    enumEachView m o data recv args blk kw
  else if bid == "Enumerator#feed" then
    if argc != 1 then enumArity m argc "1" else
    if (m.heap.get o).frozen then raiseFrozen m recv else
    let st := enumState m o
    if st.feed.isSome then .next (raiseErr m Boot.typeErrorId "feed value already set") else
    let (value, m) := if kw.isEmpty then (args.headD .nil, m) else Builtins.allocHsh m kw.toArray
    .next (withCtl (setEnumState m o { st with feed := some value }) (.value .nil))
  else if bid == "Enumerator#clone" && argc != 0 then .unsupported "Enumerator clone options" else
  if argc != 0 then enumArity m argc "0" else
  if bid == "Enumerator#size" then
    match data.size with
    | .unknown => .next (withCtl m (.value .nil))
    | .fixed v => .next (withCtl m (.value v))
    | .receiverMethod => .next (withCtl m (.send data.recv .reflective "size" [] none []))
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
        | .arr xs => .next (withCtl m (.value (.int xs.size)))
        | .hsh xs => .next (withCtl m (.value (.int xs.size)))
        | _ => .unsupported "Enumerator receiver size"
      | _ => .unsupported "Enumerator receiver size"
  else if bid == "Enumerator#inspect" then
    match Builtins.inspectP m recv with
    | .ok s => let (v, m) := Builtins.allocStr m s; .next (withCtl m (.value v))
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
      .next (withCtl m (.value v))
  else if (m.heap.get o).frozen then raiseFrozen m recv else
  if bid == "Enumerator#rewind" then
    if (enumState m o).caller.isSome then .unsupported "rewinding a running Enumerator" else
    .next (withKont m (.value data.recv) (.blkConvertK (.enumRewind o) data.recv .start))
  else enumNext m o (bid == "Enumerator#peek" || bid == "Enumerator#peek_values")
    (bid == "Enumerator#next_values" || bid == "Enumerator#peek_values")

@[rootFrameLem] theorem enumDataView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o : ObjId) (data : EnumData) (bid : String) (recv : Value)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    enumDataView (pushRootK K m) o data bid recv args blk kw =
      rootFrameR K (enumDataView m o data bid recv args blk kw) := by
  unfold enumDataView
  root_native_walk K hK
  all_goals cases hk : kw.isEmpty <;> cases hd : data.kw.isEmpty <;>
    simp only [hk, hd, Bool.false_eq_true, if_false, if_true] <;>
    root_native_walk K hK
  all_goals
    apply congrArg StepResult.next
    rw [← withCtl_frame]
    congr 1
    simp only [enumState_rootFrame]
    first
    | exact setEnumState_rootFrame K (allocHsh m kw.toArray).2 o
        {enumState m o with feed := some (allocHsh m kw.toArray).1}
    | exact setEnumState_rootFrame K m o
        {enumState m o with feed := some (args.headD .nil)}

def callEnumeratorView (m : Machine) (bid : String) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  if bid == "Object#binding" || bid == "Object#local_variables" then
    if !args.isEmpty || !kw.isEmpty then enumArity m (args.length + if kw.isEmpty then 0 else 1) "0" else
    if m.activeEnumerator.isSome && m.stack.length == 1 then
      if bid == "Object#binding" then
        .next (raiseErr m Boot.runtimeErrorId "Can't create Binding Object on top of Fiber.")
      else let (v, m) := Builtins.allocArr m #[]; .next (withCtl m (.value v))
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
      if (args.headD .nil).identEq (.sym "initialized?") then .next (withCtl m (.value (.bool initialized)))
      else match (m.heap.get o).payload with
      | .chain xs => let (v, m) := Builtins.allocArr m xs.toArray; .next (withCtl m (.value v))
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
    | .ref o => .next (withCtl m (.value (m.heap.get o).iterationResult))
    | _ => .unsupported "StopIteration result without an exception"
  else match recv with
  | .ref o =>
    if bid.endsWith "#initialize" then
      if !kw.isEmpty then .unsupported "Enumerator initializer keywords" else enumInitialize m o bid args blk
    else match (m.heap.get o).payload with
    | .enumerator none =>
      if bid == "Enumerator#inspect" && args.isEmpty && kw.isEmpty then
        let (v, m) := Builtins.allocStr m s!"#<{className m.heap (m.heap.get o).klass}: uninitialized>"
        .next (withCtl m (.value v))
      else .next (raiseErr m Boot.argumentErrorId "uninitialized enumerator")
    | .enumerator (some data) => enumDataView m o data bid recv args blk kw
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

set_option maxHeartbeats 2000000 in
@[rootFrameLem] theorem callEnumerator_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (bid : String) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    callEnumerator (pushRootK K m) bid recv args blk kw = rootFrameR K (callEnumerator m bid recv args blk kw) := by
  have hLock := hK.hashLockFree
  change callEnumeratorView (pushRootK K m) bid recv args blk kw = rootFrameR K (callEnumeratorView m bid recv args blk kw)
  unfold callEnumeratorView
  root_native_walk K hK

#print axioms callEnumerator_frame
end RubyCore.Proof.Root
