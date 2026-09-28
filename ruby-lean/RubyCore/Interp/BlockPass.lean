import RubyCore.Interp.Inspect

/-! Effectful checked conversion: block-pass to_proc (L275), String#+ to_str
(L276), splat/binding to_a/to_ary (L277), and nested parameter binding (L287). Each suspended Ruby call takes an
ordinary machine transition.
The block VM shortcut resolves a defined to_proc before checking response hooks;
String conversion uses rb_check_funcall, which checks respond_to? first. -/

namespace RubyCore.Interp

def conversionMethod : ConversionCall → String
  | .objectInspect => "instance_variables_to_inspect"
  | .block _ => "to_proc"
  | .stringPlus _ => "to_str"
  | .splat _ => "to_a"
  | .closureArgs .. | .paramDestructure .. | .forDestructure .. => "to_ary"
  | .enumRewind _ => "rewind"
  | .raiseString | .stopMessage _ | .constantSet .. => "to_str"
  | .raiseException _ => "exception"
  | .exceptionString viaToS => if viaToS then "to_s" else "to_str"

def conversionArgs : ConversionCall → List Value
  | .raiseException args => args
  | _ => []

def conversionType : ConversionCall → String
  | .objectInspect => "Array"
  | .block _ => "Proc"
  | .stringPlus _ => "String"
  | .splat _ | .closureArgs .. | .paramDestructure .. | .forDestructure .. => "Array"
  | .enumRewind _ => "Object"
  | .raiseString | .stopMessage _ | .constantSet .. => "String"
  | .raiseException _ => "Exception"
  | .exceptionString _ => "String"

/-- Continue left-to-right evaluation after expanding one splat. -/
def resumeSplat (m : Machine) (call : SplatCall) (values : List Value) : StepResult :=
  match call with
  | .args recv site name acc rest blk => startArgs m recv site name (acc ++ values) rest blk
  | .superArgs acc rest blk => startSuperArgs m (acc ++ values) rest blk
  | .yieldArgs acc rest => startYield m (acc ++ values) rest
  | .array acc rest => continueArray m (acc ++ values) rest

def blockPassProc (m : Machine) (v : Value) : Bool :=
  match v with
  | .ref o => match (m.heap.get o).payload with | .proc _ => true | _ => false
  | _ => false

def blockPassMethod (m : Machine) (v : Value) (name : String) : Option MethodDef :=
  (lookup m.heap v name).bind fun (_, md) => if md.undefined then none else some md

def blockPassNoConversion (m : Machine) (call : ConversionCall) (source : Value) : StepResult :=
  match call with
  | .objectInspect => beginObjectInspect m source .nil
  | .constantSet .. => constantNameTypeError m source
  | .exceptionString false =>
    .next (withKont m (.value source) (.blkConvertK (.exceptionString true) source .start))
  | .exceptionString true => .next (raiseErr m Boot.typeErrorId
      s!"can't convert {className m.heap (realClassOf m.heap source)} into String")
  | .raiseString =>
    .next (withKont m (.value source) (.blkConvertK (.raiseException []) source .start))
  | .raiseException _ => .next (raiseErr m Boot.typeErrorId "exception class/object expected")
  | .splat pending => resumeSplat m pending [source]
  | .closureArgs cl brk selfOv defmodOv => enterClosure m cl [source] brk selfOv defmodOv
  | .paramDestructure subs remaining body => expandParamBindings m subs [source] remaining body
  | .forDestructure targets body => finishForBindings m targets [source] body
  | .enumRewind o => .next { resetEnumerator m o with ctl := .value (.ref o) }
  | .block _ => .next (raiseErr m Boot.typeErrorId
      s!"no implicit conversion of {className m.heap (realClassOf m.heap source)} into Proc")
  | .stringPlus _ | .stopMessage _ => .next (raiseErr m Boot.typeErrorId
      s!"no implicit conversion of {Builtins.coerceName m.heap source} into String")

def blockPassInvalid (m : Machine) (call : ConversionCall) (source result : Value) : StepResult :=
  let src := className m.heap (realClassOf m.heap source)
  let dst := className m.heap (realClassOf m.heap result)
  .next (raiseErr m Boot.typeErrorId
    s!"can't convert {src} to {conversionType call} ({src}#{conversionMethod call} gives {dst})")

/-- Finish the already resolved native operation without dispatching it again:
    a converter may have mutated the receiver or redefined its operator. -/
def finishConversion (m : Machine) (call : ConversionCall) (source result : Value)
    (direct : Bool) : StepResult :=
  match call with
  | .objectInspect => beginObjectInspect m source result
  | .constantSet target value =>
    if result.identEq .nil then blockPassNoConversion m call source
    else if (Builtins.strPayload? m.heap result).isSome then finishConstantSet m target value result
    else blockPassInvalid m call source result
  | .exceptionString viaToS =>
    if result.identEq .nil && !viaToS then blockPassNoConversion m call source
    else if (Builtins.strPayload? m.heap result).isSome then .next (withCtl m (.value result))
    else blockPassInvalid m call source result
  | .raiseString =>
    if result.identEq .nil then blockPassNoConversion m call source
    else if (Builtins.strPayload? m.heap result).isSome then raiseString m result
    else blockPassInvalid m call source result
  | .stopMessage value =>
    if (Builtins.strPayload? m.heap result).isSome then newStop m none value result
    else blockPassInvalid m call source result
  | .raiseException _ =>
    if isA m.heap result Boot.exceptionId then .next (withCtl m (.jump (.raiseJ result)))
    else .next (raiseErr m Boot.typeErrorId "exception object expected")
  | .paramDestructure subs remaining body =>
    if result.identEq .nil then blockPassNoConversion m call source
    else match Builtins.arrPayload? m.heap result with
      | some xs => expandParamBindings m subs xs.toList remaining body
      | none => blockPassInvalid m call source result
  | .forDestructure targets body =>
    if result.identEq .nil then blockPassNoConversion m call source
    else match Builtins.arrPayload? m.heap result with
      | some xs => finishForBindings m targets xs.toList body
      | none => blockPassInvalid m call source result
  | .enumRewind o => .next { resetEnumerator m o with ctl := .value (.ref o) }
  | .block pending =>
    if blockPassProc m result then
      invoke m pending.recv pending.site pending.name pending.args (some result) pending.kw
    else if !direct && result.identEq .nil then blockPassNoConversion m call source
    else blockPassInvalid m call source result
  | .stringPlus recv =>
    if (Builtins.strPayload? m.heap result).isNone then blockPassInvalid m call source result
    else
      match Builtins.run "String#+" recv [result] m with
      | .ok v m => .next (withCtl m (.value v))
      | .err cls msg m => .next (raiseErr m cls msg)
      | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
      | .frozen recv m => raiseFrozen m recv
      | .unsupported r => .unsupported r
  | .splat pending =>
    if result.identEq .nil then blockPassNoConversion m call source
    else match Builtins.arrPayload? m.heap result with
      | some xs => resumeSplat m pending xs.toList
      | none => blockPassInvalid m call source result
  | .closureArgs cl brk selfOv defmodOv =>
    if result.identEq .nil then blockPassNoConversion m call source
    else match Builtins.arrPayload? m.heap result with
      | some xs => enterClosure m cl xs.toList brk selfOv defmodOv
      | none => blockPassInvalid m call source result

/-- Only a custom handler is called by checked conversion. Its NoMethodError
    is conditionally rescued by the continuation, not by ordinary dispatch. -/
def blockPassMissing (m : Machine) (call : ConversionCall) (source : Value)
    (respond respondMissing : Bool) : StepResult :=
  match lookup m.heap source "method_missing" with
  | some (owner, md) =>
    if md.undefined || md.builtin == some "BasicObject#method_missing" then
      blockPassNoConversion m call source
    else
      let m := { m with missingReason := .ordinary }
      invoke (withKont m m.ctl (.blkConvertK call source (.missing owner respond respondMissing)))
        source .reflective "method_missing" (.sym (conversionMethod call) :: conversionArgs call) none
  | none => blockPassNoConversion m call source

/-- Response hooks may install the converter, so repeat lookup after them. -/
def blockPassChecked (m : Machine) (call : ConversionCall) (source : Value)
    (promised : Bool) : StepResult :=
  let name := conversionMethod call
  match blockPassMethod m source name with
  | some _ =>
    invoke (withKont m m.ctl (.blkConvertK call source (.converted false)))
      source .reflective name (conversionArgs call) none
  | none =>
    if (lookup m.heap source name).isNone &&
        (crubyShadow m.heap (ancestors m.heap (classOf m.heap source)) name).isSome then
      .unsupported s!"checked conversion: unmodeled native {name}"
    else
      match blockPassMethod m source "respond_to_missing?" with
      | some md =>
        if md.builtin == some "Object#respond_to_missing?" then
          blockPassMissing m call source promised false
        else
          invoke (withKont m m.ctl (.blkConvertK call source (.respondMissing promised)))
            source .reflective "respond_to_missing?" [.sym name, .bool true] none
      | none => blockPassMissing m call source promised false

/-- Fixed-arity-one respond_to? gets one argument; other supported signatures
    get the name and include_private=true, matching CRuby's checked calls. -/
def blockPassRespond (m : Machine) (call : ConversionCall) (source : Value)
    (md : MethodDef) : StepResult :=
  if md.builtin.isSome then
    .unsupported "checked conversion: builtin alias for respond_to? needs native arity"
  else
    let required := md.params.countP fun p => match p with
      | .req _ | .destr _ => true | _ => false
    let variadic := md.params.any fun p => match p with
      | .opt .. | .rest _ | .fwd => true | _ => false
    let keywords := md.params.any fun p => match p with
      | .key .. | .kwrest _ => true | _ => false
    if keywords then .unsupported "checked conversion: keyword respond_to? arity"
    else if !variadic && required > 2 then
      .next (raiseErr m Boot.argumentErrorId
        s!"respond_to? must accept 1 or 2 arguments (requires {required})")
    else
      let args := if !variadic && required == 1 then [.sym (conversionMethod call)]
        else [.sym (conversionMethod call), .bool true]
      invoke (withKont m m.ctl (.blkConvertK call source .respond))
        source .reflective "respond_to?" args none

def startCheckedConversion (m : Machine) (call : ConversionCall) (source : Value) : StepResult :=
  match blockPassMethod m source "respond_to?" with
  | some md => blockPassRespond m call source md
  | none => blockPassChecked m call source false

/-- VM splat bypasses nil and actual Arrays; every other value is checked via
    to_a, including native Hash/Range/MatchData conversions and their overrides. -/
def startSplat (m : Machine) (call : SplatCall) (source : Value) : StepResult :=
  if source.identEq .nil then resumeSplat m call []
  else match Builtins.arrPayload? m.heap source with
    | some xs => resumeSplat m call xs.toList
    | none => startCheckedConversion m (.splat call) source

/-- Proc and nil bypass lookup; a defined to_proc also bypasses response hooks. -/
def coerceBlockPass (m : Machine) (call : BlockPassCall) (source : Value) : StepResult :=
  if source.identEq .nil then
    invoke m call.recv call.site call.name call.args none call.kw
  else if blockPassProc m source then
    invoke m call.recv call.site call.name call.args (some source) call.kw
  else
    match blockPassMethod m source "to_proc" with
    | some _ =>
      invoke (withKont m m.ctl (.blkConvertK (.block call) source (.converted true)))
        source .reflective "to_proc" [] none
    | none => startCheckedConversion m (.block call) source

def resumeBlockPass (m : Machine) (call : ConversionCall) (source : Value)
    (phase : BlockPassPhase) (result : Value) : StepResult :=
  match phase with
  | .start => startCheckedConversion m call source
  | .respond =>
    if result.truthy then blockPassChecked m call source true
    else blockPassNoConversion m call source
  | .respondMissing promised =>
    if result.truthy then blockPassMissing m call source promised true
    else blockPassNoConversion m call source
  | .converted direct => finishConversion m call source result direct
  | .missing .. => finishConversion m call source result false

def unwindBlockPass (m : Machine) (call : ConversionCall) (source : Value)
    (phase : BlockPassPhase) (j : Jump) : StepResult :=
  match phase, j with
  | .missing owner respond respondMissing, .raiseJ exc =>
    let bound := match methodOn m.heap owner (conversionMethod call) with
      | some (_, md) => !md.undefined | none => false
    if isA m.heap exc Boot.noMethodErrorId && !respond && (bound || !respondMissing) then
      blockPassNoConversion m call source
    else .next (withCtl m (.jump j))
  | _, _ => .next (withCtl m (.jump j))

end RubyCore.Interp
