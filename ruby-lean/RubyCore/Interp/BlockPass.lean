import RubyCore.Interp.Send

/-! Effectful `&operand` conversion. Follows CRuby's vm_to_proc and checked
conversion on a lookup miss; each helper takes one transition (L275). -/

namespace RubyCore.Interp

def blockPassProc (m : Machine) (v : Value) : Bool :=
  match v with
  | .ref o => match (m.heap.get o).payload with | .proc _ => true | _ => false
  | _ => false

def blockPassMethod (m : Machine) (v : Value) (name : String) : Option MethodDef :=
  (lookup m.heap v name).bind fun (_, md) => if md.undefined then none else some md

def blockPassNoConversion (m : Machine) (source : Value) : StepResult :=
  let desc := className m.heap (realClassOf m.heap source)
  .next (raiseErr m Boot.typeErrorId s!"no implicit conversion of {desc} into Proc")

def blockPassInvalid (m : Machine) (source result : Value) : StepResult :=
  let src := className m.heap (realClassOf m.heap source)
  let dst := className m.heap (realClassOf m.heap result)
  .next (raiseErr m Boot.typeErrorId s!"can't convert {src} to Proc ({src}#to_proc gives {dst})")

/-- Only a user missing-method handler is called by checked conversion. Its
    NoMethodError is conditionally rescued by the continuation, not by invoke. -/
def blockPassMissing (m : Machine) (call : BlockPassCall) (source : Value)
    (respond respondMissing : Bool) : StepResult :=
  match lookup m.heap source "method_missing" with
  | some (owner, md) =>
    if md.undefined then blockPassNoConversion m source
    else
      invoke (withKont m m.ctl (.blkConvertK call source (.missing owner respond respondMissing)))
        source .reflective "method_missing" [.sym "to_proc"] none
  | none => blockPassNoConversion m source

/-- The response hook may install to_proc, so repeat lookup after respond_to?. -/
def blockPassChecked (m : Machine) (call : BlockPassCall) (source : Value)
    (promised : Bool) : StepResult :=
  match blockPassMethod m source "to_proc" with
  | some _ =>
    invoke (withKont m m.ctl (.blkConvertK call source (.converted false)))
      source .reflective "to_proc" [] none
  | none =>
    match blockPassMethod m source "respond_to_missing?" with
    | some md =>
      if md.builtin == some "Object#respond_to_missing?" then
        blockPassMissing m call source promised false
      else
        invoke (withKont m m.ctl (.blkConvertK call source (.respondMissing promised)))
          source .reflective "respond_to_missing?" [.sym "to_proc", .bool true] none
    | none => blockPassMissing m call source promised false

/-- CRuby passes one argument to a fixed-arity-one respond_to? override, two
    otherwise, and rejects a fixed arity greater than two before calling it. -/
def blockPassRespond (m : Machine) (call : BlockPassCall) (source : Value)
    (md : MethodDef) : StepResult :=
  if md.builtin.isSome then
    .unsupported "block conversion: builtin alias for respond_to? needs native arity"
  else
    let required := md.params.countP fun p => match p with
      | .req _ | .destr _ => true | _ => false
    let variadic := md.params.any fun p => match p with
      | .opt .. | .rest _ | .fwd => true | _ => false
    let keywords := md.params.any fun p => match p with
      | .key .. | .kwrest _ => true | _ => false
    if keywords then .unsupported "block conversion: keyword respond_to? arity"
    else if !variadic && required > 2 then
      .next (raiseErr m Boot.argumentErrorId
        s!"respond_to? must accept 1 or 2 arguments (requires {required})")
    else
      let args := if !variadic && required == 1 then [.sym "to_proc"]
        else [.sym "to_proc", .bool true]
      invoke (withKont m m.ctl (.blkConvertK call source .respond))
        source .reflective "respond_to?" args none

/-- Proc and nil bypass lookup. Every other value resolves to_proc first,
    including private entries. Only a miss consults the response hooks. -/
def coerceBlockPass (m : Machine) (call : BlockPassCall) (source : Value) : StepResult :=
  if source.identEq .nil then
    invoke m call.recv call.site call.name call.args none call.kw
  else if blockPassProc m source then
    invoke m call.recv call.site call.name call.args (some source) call.kw
  else
    match blockPassMethod m source "to_proc" with
    | some _ =>
      invoke (withKont m m.ctl (.blkConvertK call source (.converted true)))
        source .reflective "to_proc" [] none
    | none =>
      -- A tombstone really removes the CRuby method; a bare model miss may
      -- instead name an unmodeled native method (e.g. Method#to_proc).
      if (lookup m.heap source "to_proc").isNone &&
          (crubyShadow m.heap (ancestors m.heap (classOf m.heap source)) "to_proc").isSome then
        .unsupported "block conversion: unmodeled native to_proc"
      else
        match blockPassMethod m source "respond_to?" with
        | some md => blockPassRespond m call source md
        | none => blockPassChecked m call source false

def resumeBlockPass (m : Machine) (call : BlockPassCall) (source : Value)
    (phase : BlockPassPhase) (result : Value) : StepResult :=
  match phase with
  | .respond =>
    if result.truthy then blockPassChecked m call source true
    else blockPassNoConversion m source
  | .respondMissing promised =>
    if result.truthy then blockPassMissing m call source promised true
    else blockPassNoConversion m source
  | .converted direct =>
    if blockPassProc m result then
      invoke m call.recv call.site call.name call.args (some result) call.kw
    else if !direct && result.identEq .nil then blockPassNoConversion m source
    else blockPassInvalid m source result
  | .missing .. =>
    if blockPassProc m result then
      invoke m call.recv call.site call.name call.args (some result) call.kw
    else if result.identEq .nil then blockPassNoConversion m source
    else blockPassInvalid m source result

def unwindBlockPass (m : Machine) (source : Value) (phase : BlockPassPhase)
    (j : Jump) : StepResult :=
  match phase, j with
  | .missing owner respond respondMissing, .raiseJ exc =>
    let bound := match methodOn m.heap owner "to_proc" with
      | some (_, md) => !md.undefined | none => false
    if isA m.heap exc Boot.noMethodErrorId && !respond && (bound || !respondMissing) then
      blockPassNoConversion m source
    else .next (withCtl m (.jump j))
  | _, _ => .next (withCtl m (.jump j))

end RubyCore.Interp
