import RubyCore.Interp.Send

/-! Native object inspection (L289): checked selection hook, buffered field names,
    live values/filter, ordinary nested inspect/to_s and an unwind-safe recursion
    guard. Ruby overrides of instance_variables/get are not part of this protocol. -/

namespace RubyCore.Interp

private def inspectedString (m : Machine) (text : String) : StepResult :=
  let (str, m) := Builtins.allocStr m text
  .next (withCtl m (.value str))

/-- The names are buffered at entry; each value and the selection Array stay live.
    A leading '-' marks an empty field list until its first field is appended. -/
def continueObjectInspect (m : Machine) (recv filter : Value) (remaining : List String)
    (text : String) : StepResult :=
  match remaining with
  | [] => inspectedString m ("#" ++ String.ofList (text.toList.drop 1) ++ ">")
  | name :: more =>
    let selected := filter.identEq .nil ||
      (Builtins.arrPayload? m.heap filter).any (fun xs => xs.any (·.identEq (.sym name)))
    let value := match recv with
      | .ref o => ((m.heap.get o).ivars.find? (·.1 == name)).map (·.2)
      | _ => none
    match value with
    | none => continueObjectInspect m recv filter more text
    | some value =>
      if !selected then continueObjectInspect m recv filter more text else
      let lead := if text.startsWith "-" then
        "#" ++ String.ofList (text.toList.drop 1) ++ " " else text ++ ", "
      invoke (withKont m m.ctl (.objectInspectK recv filter more (lead ++ name ++ "=") none))
        value .reflective "inspect" [] none

/-- The checked hook runs before recursion detection, as in rb_obj_inspect. -/
def beginObjectInspect (m : Machine) (recv filter : Value) : StepResult :=
  let fields := match recv with
    | .ref o => (m.heap.get o).ivars.reverse.map (·.1)
    | _ => []
  let count := if filter.identEq .nil then some fields.length
    else (Builtins.arrPayload? m.heap filter).map (·.size)
  match count with
  | none => .next (raiseErr m Boot.typeErrorId
      s!"Expected #instance_variables_to_inspect to return an Array or nil, but it returned {className m.heap (realClassOf m.heap filter)}")
  | some count => match recv with
    | .ref o =>
      let head := s!"-<{className m.heap (realClassOf m.heap recv)}:{fakeAddr o}"
      if count == 0 then continueObjectInspect m recv filter [] head
      else if m.kont.any (fun k => match k with
          | .objectInspectK other .. => recv.identEq other
          | _ => false) then
        continueObjectInspect m recv filter [] (head ++ " ...")
      else continueObjectInspect m recv filter fields head
    | _ => .unsupported "native Object#inspect of an immediate"

def resumeObjectInspect (m : Machine) (recv filter : Value) (remaining : List String)
    (text : String) (stringifying : Option Value) (value : Value) : StepResult :=
  match Builtins.strPayload? m.heap value with
  | some suffix =>
    if Builtins.isBinaryStr m.heap value && hasHighByte suffix then
      .unsupported "object inspection containing non-UTF-8 bytes"
    else continueObjectInspect m recv filter remaining (text ++ suffix)
  | none => match stringifying with
    | none =>
      invoke (withKont m m.ctl (.objectInspectK recv filter remaining text (some value)))
        value .reflective "to_s" [] none
    | some source =>
      match Builtins.run "Object#__any_to_s" source [] m with
      | .ok str m => match Builtins.strPayload? m.heap str with
        | some suffix => continueObjectInspect m recv filter remaining (text ++ suffix)
        | none => .stuck "native default inspection did not produce a String"
      | .err cls msg m => .next (raiseErr m cls msg)
      | .throwV exc m => .next (withCtl m (.jump (.raiseJ exc)))
      | .frozen recv m => raiseFrozen m recv
      | .unsupported reason => .unsupported reason

end RubyCore.Interp
