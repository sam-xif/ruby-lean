import RubyCore.Interp.Send

/-! Effectful frozen-error construction: render the class, initialize with a
mutable message, inspect the receiver, then append to that same message (L286). -/

namespace RubyCore.Interp

/-- Native String append bypasses Ruby overrides, but checks the live frozen
    bit. The initializer may have replaced the exception's message entirely. -/
def finishFrozen (m : Machine) (exc message value : Value) : StepResult :=
  match message, Builtins.strPayload? m.heap value with
  | .ref p, some str =>
    if Builtins.isBinaryStr m.heap value && hasHighByte str then
      .unsupported "FrozenError message containing non-UTF-8 bytes"
    else if (m.heap.get p).frozen then raiseFrozen m message
    else match (m.heap.get p).payload with
      | .str pre =>
        let h := m.heap.set p { m.heap.get p with payload := .str (pre ++ str) }
        .next { m with heap := h, ctl := .jump (.raiseJ exc) }
      | _ => .unsupported "FrozenError message is not a String"
  | _, _ => .unsupported "FrozenError renderer did not produce a String"

/-- Initialize before receiver inspection and before entering its recursion
    guard. CRuby appends to the same mutable String passed to initialize. -/
def beginFrozenInit (m : Machine) (recv name : Value) : StepResult :=
  match Builtins.strPayload? m.heap name with
  | none => .unsupported "FrozenError class name is not a String"
  | some cls =>
    if Builtins.isBinaryStr m.heap name && hasHighByte cls then
      .unsupported "FrozenError class name containing non-UTF-8 bytes"
    else
      let (message, m) := Builtins.allocStr m s!"can't modify frozen {cls}: "
      let (o, h) := m.heap.alloc { klass := Boot.frozenErrorId, payload := .exc .nil }
      invoke (withKont { m with heap := h } m.ctl (.frozenErrorK recv (.initialized (.ref o) message)))
        (.ref o) .reflective "initialize" [message] none

def resumeFrozen (m : Machine) (recv : Value) (phase : FrozenPhase)
    (value : Value) : StepResult :=
  match phase with
  | .start =>
    invoke (withKont m m.ctl (.frozenErrorK recv .className))
      (.ref (realClassOf m.heap recv)) .reflective "to_s" [] none
  | .className =>
    if (Builtins.strPayload? m.heap value).isSome then beginFrozenInit m recv value
    else
      match Builtins.run "Object#__any_to_s" (.ref (realClassOf m.heap recv)) [] m with
      | .ok value m => beginFrozenInit m recv value
      | .err k msg m => .next (raiseErr m k msg)
      | .throwV exc m => .next (withCtl m (.jump (.raiseJ exc)))
      | .frozen recv m => raiseFrozen m recv
      | .unsupported reason => .unsupported reason
  | .initialized exc message =>
    -- Setting CRuby's native receiver metadata checks the exception's frozen bit.
    if (match exc with | .ref o => (m.heap.get o).frozen | _ => false) then
      raiseFrozen m exc
    else if m.kont.any (fun k => match k with
        | .frozenErrorK other (.inspected ..)
        | .frozenErrorK other (.stringified ..) => recv.identEq other
        | _ => false) then
      let (tail, m) := Builtins.allocStr m " ..."
      finishFrozen m exc message tail
    else invoke (withKont m m.ctl (.frozenErrorK recv (.inspected exc message)))
      recv .reflective "inspect" [] none
  | .inspected exc message =>
    if (Builtins.strPayload? m.heap value).isSome then finishFrozen m exc message value
    else invoke (withKont m m.ctl (.frozenErrorK recv (.stringified exc message value)))
      value .reflective "to_s" [] none
  | .stringified exc message source =>
    if (Builtins.strPayload? m.heap value).isSome then finishFrozen m exc message value
    else
      match Builtins.run "Object#__any_to_s" source [] m with
      | .ok value m => finishFrozen m exc message value
      | .err k msg m => .next (raiseErr m k msg)
      | .throwV exc m => .next (withCtl m (.jump (.raiseJ exc)))
      | .frozen recv m => raiseFrozen m recv
      | .unsupported reason => .unsupported reason

end RubyCore.Interp
