/-
The observation (Semantics 00 §2).

What a finished run is observed as: everything written to standard output, the
`inspect` of the final value, and the class and message of an uncaught
exception. This is what the differential tests compare with CRuby.
-/
import RubyCore.Interp
import Json

namespace RubyCore

-- `Json` is this project's vendored copy of Lean's (`Json.lean`), at the root
-- namespace, so there is nothing to open.

inductive ObsResult where
  /-- A comparable observation (JSON matching Observation.to_json). -/
  | obs (j : Json)
  /-- Out of the modeled fragment, with a reason (SUT exit 3). -/
  | unsupported (reason : String)
  /-- The model itself is broken (stuck state) — a harness error, never
      silently mapped to Unsupported-by-design. Still exits 3 but the
      reason is prefixed so triage can spot it. -/
  | stuck (msg : String)

def obsJson (stdout : String) (result : Option String)
    (exc : Option (String × String)) : Json :=
  Json.mkObj [
    ("stdout", Json.str stdout),
    ("result_repr", match result with
      | some r => Json.str r
      | none => Json.null),
    ("exception", match exc with
      | some (c, msg) => Json.arr #[Json.str c, Json.str msg]
      | none => Json.null),
    ("timed_out", Json.bool false)
  ]

/-- Observation is an effectful phase, just like the CRuby harness wrapper:
    sends run on the completed heap with the program's lexical captures intact. -/
def observationSend (fuel : Nat) (m : Machine) (recv : Value) (name : String) : Interp.RunResult :=
  let m := { m with kont := [], currentExc := none }
  match Interp.invoke m recv .explicit name [] none with
  | .next m => Interp.run fuel m
  | .done v m => .value v m
  | .uncaught e m => .uncaught e m
  | .unsupported reason => .unsupported reason m
  | .stuck reason => .stuck reason m

def observationStopped : Interp.RunResult → ObsResult
  | .unsupported reason _ => .unsupported reason
  | .outOfFuel _ => .unsupported "out of fuel during observation"
  | .stuck reason _ => .stuck reason
  | .uncaught _ _ => .unsupported "exception escaped the observation wrapper"
  | .value _ _ => .stuck "observation expected a stopped computation"

/-- Byte strings that cannot be represented in our JSON transport remain explicit
    gates; dispatching repr must not silently change their encoding. -/
def observationString (m : Machine) (value : Value) : Except String String :=
  match Builtins.strPayload? m.heap value with
  | some s =>
    if Builtins.isBinaryStr m.heap value && hasHighByte s then
      .error "observation String contains non-UTF-8 bytes"
    else .ok s
  | none => .error "observation method returned a non-String"

def observeExceptionMessage (fuel : Nat) (m : Machine) (exc : Value) (cls : String) : ObsResult :=
  match observationSend fuel m exc "message" with
  | .value message m =>
    match observationSend fuel m message "to_s" with
    | .value message m =>
      match observationString m message with
      | .ok str => .obs (obsJson m.out none (some (cls, str)))
      | .error reason => .unsupported reason
    | .uncaught _ m => .obs (obsJson m.out none (some (cls, "<unmessageable>")))
    | stopped => observationStopped stopped
  | .uncaught _ m => .obs (obsJson m.out none (some (cls, "<unmessageable>")))
  | stopped => observationStopped stopped

def observeException (fuel : Nat) (m : Machine) (exc : Value) : ObsResult :=
  -- Match the wrapper's exc.class.name.to_s sends, including user overrides and
  -- anonymous exception classes. This portion is outside its message rescue.
  match observationSend fuel m exc "class" with
  | .value klass m =>
    match observationSend fuel m klass "name" with
    | .value name m =>
      match observationSend fuel m name "to_s" with
      | .value name m =>
        match observationString m name with
        | .ok str => observeExceptionMessage fuel m exc str
        | .error reason => .unsupported reason
      | stopped => observationStopped stopped
    | stopped => observationStopped stopped
  | stopped => observationStopped stopped

def observe (r : Interp.RunResult) (fuel : Nat := 100000) : ObsResult :=
  match r with
  | .value value m =>
    match observationSend fuel m value "inspect" with
    | .value repr m =>
      if repr.identEq .nil then .obs (obsJson m.out none none)
      else match observationString m repr with
        | .ok str => .obs (obsJson m.out (some str) none)
        | .error reason => .unsupported reason
    | .uncaught _ m => .obs (obsJson m.out (some "<uninspectable>") none)
    | stopped => observationStopped stopped
  | .uncaught exc m => observeException fuel m exc
  | .unsupported reason _ => .unsupported reason
  | .outOfFuel _ => .unsupported "out of fuel"
  | .stuck msg _ => .stuck msg

end RubyCore
