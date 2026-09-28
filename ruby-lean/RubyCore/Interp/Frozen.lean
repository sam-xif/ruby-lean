import RubyCore.Interp.Send

/-! Effectful frozen-error rendering: class name, inspect, and String conversion. -/

namespace RubyCore.Interp

/-- Complete CRuby's rb_inspect/rb_obj_as_string path before raising the
    mutation error. Exceptions and nonlocal exits from either method propagate. -/
def finishFrozen (m : Machine) (cls : String) (value : Value) : StepResult :=
  match Builtins.strPayload? m.heap value with
  | some str =>
    if Builtins.isBinaryStr m.heap value && hasHighByte str then
      .unsupported "FrozenError message containing non-UTF-8 bytes"
    else .next (raiseErr m Boot.frozenErrorId s!"can't modify frozen {cls}: {str}")
  | none => .unsupported "FrozenError renderer did not produce a String"

/-- Class rendering precedes CRuby's recursion guard on receiver inspection. -/
def beginFrozenInspect (m : Machine) (recv name : Value) : StepResult :=
  match Builtins.strPayload? m.heap name with
  | none => .unsupported "FrozenError class name is not a String"
  | some cls =>
    if Builtins.isBinaryStr m.heap name && hasHighByte cls then
      .unsupported "FrozenError class name containing non-UTF-8 bytes"
    else if m.kont.any (fun k => match k with
        | .frozenErrorK other _ .inspected
        | .frozenErrorK other _ (.stringified _) => recv.identEq other
        | _ => false) then
      .next (raiseErr m Boot.frozenErrorId s!"can't modify frozen {cls}:  ...")
    else invoke (withKont m m.ctl (.frozenErrorK recv cls .inspected))
      recv .reflective "inspect" [] none

def resumeFrozen (m : Machine) (recv : Value) (cls : String)
    (phase : FrozenPhase) (value : Value) : StepResult :=
  match phase with
  | .start =>
    invoke (withKont m m.ctl (.frozenErrorK recv cls .className))
      (.ref (realClassOf m.heap recv)) .reflective "to_s" [] none
  | .className =>
    if (Builtins.strPayload? m.heap value).isSome then beginFrozenInspect m recv value
    else
      match Builtins.run "Object#__any_to_s" (.ref (realClassOf m.heap recv)) [] m with
      | .ok value m => beginFrozenInspect m recv value
      | .err k msg m => .next (raiseErr m k msg)
      | .throwV exc m => .next (withCtl m (.jump (.raiseJ exc)))
      | .frozen recv m => raiseFrozen m recv
      | .unsupported reason => .unsupported reason
  | .inspected =>
    if (Builtins.strPayload? m.heap value).isSome then finishFrozen m cls value
    else invoke (withKont m m.ctl (.frozenErrorK recv cls (.stringified value)))
      value .reflective "to_s" [] none
  | .stringified source =>
    if (Builtins.strPayload? m.heap value).isSome then finishFrozen m cls value
    else
      match Builtins.run "Object#__any_to_s" source [] m with
      | .ok value m => finishFrozen m cls value
      | .err k msg m => .next (raiseErr m k msg)
      | .throwV exc m => .next (withCtl m (.jump (.raiseJ exc)))
      | .frozen recv m => raiseFrozen m recv
      | .unsupported reason => .unsupported reason

end RubyCore.Interp
