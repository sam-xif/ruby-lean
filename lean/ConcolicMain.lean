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
import RubyCore.Concolic.Shadow

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

/-- Run the program, advancing the **symbolic shadow** in lockstep (S1 of
    `docs/semantics/concolic-dataflow.md`) so each branch carries its condition as
    a term over the inputs, and classify the outcome. -/
partial def collect (inputs : List Int) (steps maxSteps : Nat)
    (acc : Array Json) (risks : Array Json) (s : SymState) (m : Machine) :
    Array Json × Array Json × Json × List String :=
  if steps ≥ maxSteps then
    (acc, risks, Json.mkObj [("kind", Json.str "outoffuel"),
                      ("detail", Json.str s!"step cap {maxSteps} reached")], s.notes)
  else
    match stepFn m with
    | .next m' =>
      let (s', ev?, risk?) := symStep inputs m m' s
      let acc := match ev? with
        | some ev => acc.push ev.toJson
        | none => acc
      let risks := match risk? with
        | some r => risks.push r.toJson
        | none => risks
      collect inputs (steps + 1) maxSteps acc risks s' m'
    | .done v m' =>
      (acc, risks, Json.mkObj [("kind", Json.str "value"),
                        ("detail", Json.str ((RubyCore.inspect m'.heap v).toOption.getD "?")),
                        ("stdout", Json.str m'.out)], s.notes)
    | .uncaught exc m' =>
      let cls := className m'.heap (classOf m'.heap exc)
      let msg := match (m'.heap.get (match exc with | .ref o => o | _ => 0)).payload with
        | .exc s => s
        | _ => ""
      (acc, risks, Json.mkObj [
        ("kind", Json.str (if isTypeError m'.heap exc then "typestuck" else "uncaught")),
        ("class", Json.str cls), ("message", Json.str msg),
        ("stdout", Json.str m'.out)], s.notes)
    | .unsupported r =>
      (acc, risks, Json.mkObj [("kind", Json.str "unsupported"), ("detail", Json.str r)], s.notes)
    | .stuck msg =>
      (acc, risks, Json.mkObj [("kind", Json.str "stuck"), ("detail", Json.str msg)], s.notes)

end RubyCore.Concolic

/-- CLI: `rubycore-concolic [maxSteps] [--inputs n1,n2,…] < program.json`.
    Inputs are bound to the reserved globals `$__in0`, `$__in1`, … (§6.5), so no
    AST rewriting is needed to supply them. -/
def parseInputs (args : List String) : List Int :=
  match args.dropWhile (· != "--inputs") with
  | _ :: spec :: _ =>
    (spec.splitOn ",").filterMap fun t =>
      let t := t.trimAscii
      if t.startsWith "-" then (t.drop 1).toString.toNat?.map (fun n => -(Int.ofNat n))
      else t.toNat?.map Int.ofNat
  | _ => []

def main (args : List String) : IO UInt32 := do
  let inputs := parseInputs args
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
      let m0 := RubyCore.Concolic.initMachine prog inputs
      let s0 := RubyCore.Concolic.initSym inputs
      let (branches, risks, outcome, notes) :=
        RubyCore.Concolic.collect inputs 0 maxSteps #[] #[] s0 m0
      IO.println (Json.mkObj [
        ("branches", Json.arr branches),
        ("dispatchrisks", Json.arr risks),
        ("outcome", outcome),
        ("frontier", Json.arr (notes.map Json.str).toArray)]).compress
      return 0
