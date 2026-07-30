/-
`rubycore-concolic` — the concolic **trace** executable (Direction-A engine support).

Runs a RubyCore program through the *real* `stepFn` and emits, as JSON:

  * `branches` — the branch decisions taken, in order (`if`/`while`, and which way)
  * `outcome`  — the authoritative classification of the run, including whether it
                 ended **type-stuck** (uncaught NoMethodError/ArgumentError/
                 TypeError, closed under subclassing via `isA`)

Why this exists (see `concolic/implementation-notes.md` K9): the concolic engine
previously carried its *own* interpreter, including hand-copied method tables — so
the component deciding "is this a type error?" was a duplicate of the model and
could silently drift from it. With this trace mode, **the Lean semantics is the
executor and the sole arbiter of outcomes**; the outside engine only computes
symbolic terms and calls the solver. As the model grows toward full Ruby, the
engine inherits that coverage for free instead of having to chase it.

IMPORTANT — no SUT changes. Branch decisions are *observable at the configuration
level*: a decision happens exactly when the control is a value and the top
continuation is `ifK`/`whileCondK`, and `Value.truthy` says which way it goes. So
this needs no instrumentation inside `stepFn` (which stays the difftested
artifact), and it is a separate executable, off the default build target, so
`rubycore` is untouched.

Usage (stdin = the same versioned RubyCore JSON `bin/export-json` emits):
    rubycore-concolic [maxSteps] < program.json
-/
import RubyCore

open Lean (Json)
open RubyCore
open RubyCore.Interp

namespace RubyCore.Concolic

/-- The type-error family of `type-safety-by-reachability.md` §2 / `typeErrorFamily`
    in `Proof/TypeSafety.lean`. Membership is by `isA`, so it is closed under
    user subclassing. -/
def typeErrorFamily : List ObjId :=
  [Boot.noMethodErrorId, Boot.argumentErrorId, Boot.typeErrorId]

def isTypeError (h : Heap) (exc : Value) : Bool :=
  typeErrorFamily.any (fun k => isA h exc k)

/-- A branch decision observed at the configuration level: the control is a value
    and the top kont is a conditional. `Value.truthy` decides the direction, so no
    instrumentation inside `stepFn` is required. -/
def branchEvent (m : Machine) : Option Json :=
  match m.ctl, m.kont with
  | .value v, (.ifK _ _) :: _ =>
    some (Json.mkObj [("kind", Json.str "if"), ("taken", Json.bool v.truthy)])
  | .value v, (.whileCondK _ _) :: _ =>
    some (Json.mkObj [("kind", Json.str "while"), ("taken", Json.bool v.truthy)])
  | _, _ => none

/-- Run the program, accumulating branch events; classify the outcome. -/
partial def collect (steps maxSteps : Nat) (acc : Array Json) (m : Machine) :
    Array Json × Json :=
  if steps ≥ maxSteps then
    (acc, Json.mkObj [("kind", Json.str "outoffuel"),
                      ("detail", Json.str s!"step cap {maxSteps} reached")])
  else
    let acc := match branchEvent m with
      | some e => acc.push e
      | none => acc
    match stepFn m with
    | .next m' => collect (steps + 1) maxSteps acc m'
    | .done v m' =>
      (acc, Json.mkObj [("kind", Json.str "value"),
                        ("detail", Json.str ((RubyCore.inspect m'.heap v).toOption.getD "?")),
                        ("stdout", Json.str m'.out)])
    | .uncaught exc m' =>
      let cls := className m'.heap (classOf m'.heap exc)
      let msg := match (m'.heap.get (match exc with | .ref o => o | _ => 0)).payload with
        | .exc s => s
        | _ => ""
      (acc, Json.mkObj [
        ("kind", Json.str (if isTypeError m'.heap exc then "typestuck" else "uncaught")),
        ("class", Json.str cls), ("message", Json.str msg),
        ("stdout", Json.str m'.out)])
    | .unsupported r =>
      (acc, Json.mkObj [("kind", Json.str "unsupported"), ("detail", Json.str r)])
    | .stuck msg =>
      (acc, Json.mkObj [("kind", Json.str "stuck"), ("detail", Json.str msg)])

end RubyCore.Concolic

def main (args : List String) : IO UInt32 := do
  let maxSteps := (args.head?.bind (·.toNat?)).getD 500000
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input with
  | .error e => IO.eprintln s!"bad JSON: {e}"; return 1
  | .ok j =>
    match Decode.program j with
    | .error e =>
      -- keep the harness's Unsupported gate distinguishable from a real failure
      if e.startsWith "UNSUPPORTED: " then
        IO.println (Json.mkObj [("branches", Json.arr #[]),
          ("outcome", Json.mkObj [("kind", Json.str "unsupported"),
                                  ("detail", Json.str ((e.drop 13).toString))])]).compress
        return 0
      IO.eprintln s!"decode error: {e}"; return 1
    | .ok prog =>
      let (branches, outcome) :=
        RubyCore.Concolic.collect 0 maxSteps #[] (Machine.init prog)
      IO.println (Json.mkObj [("branches", Json.arr branches),
                              ("outcome", outcome)]).compress
      return 0
