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

/-- **The bad-state family is a campaign parameter** (`druby-reproduction-plan.md`
    §4.1). "One checker, pluggable bad-state predicate" is the standing thesis; this
    is where it is cashed out for Direction A.

    - `typeOnly` — `typeErrorFamily` of `type-safety-by-reachability.md` §2 /
      `Proof/TypeSafety.lean`: NoMethodError ∪ ArgumentError ∪ TypeError. The
      default, and the only family with metatheory attached.
    - `typeAndName` — additionally a bare `NameError` (undefined local/constant).
      Deliberately *not* the default: a `NameError` is not a type error under our
      definition, and `TypeSafety.lean` §1 says so. It is the class DRuby's ai4r
      and vimrecover errors land in, so reporting those needs this family.

    Note NoMethodError ⊂ NameError, so `typeAndName` subsumes the NoMethodError
    entry; both are listed for clarity, and `isA` makes the overlap harmless. -/
inductive BadStateFamily where
  | typeOnly | typeAndName
deriving Repr, DecidableEq, Inhabited

def BadStateFamily.ids : BadStateFamily → List ObjId
  | .typeOnly => [Boot.noMethodErrorId, Boot.argumentErrorId, Boot.typeErrorId]
  | .typeAndName =>
    [Boot.noMethodErrorId, Boot.argumentErrorId, Boot.typeErrorId, Boot.nameErrorId]

def BadStateFamily.ofString : String → Option BadStateFamily
  | "type" => some .typeOnly
  | "type+name" => some .typeAndName
  | _ => none

def BadStateFamily.name : BadStateFamily → String
  | .typeOnly => "type" | .typeAndName => "type+name"

def isTypeError (fam : BadStateFamily) (h : Heap) (exc : Value) : Bool :=
  fam.ids.any (fun k => isA h exc k)

/-- Run the program, advancing the **symbolic shadow** in lockstep (S1 of
    `docs/semantics/concolic-dataflow.md`) so each branch carries its condition as
    a term over the inputs, and classify the outcome. -/
partial def collect (fam : BadStateFamily) (inputs : List SymVal) (steps maxSteps : Nat)
    (acc : Array Json) (risks : Array Json) (doms : Array Json)
    (s : SymState) (m : Machine) :
    Array Json × Array Json × Array Json × Json × List String :=
  if steps ≥ maxSteps then
    (acc, risks, doms, Json.mkObj [("kind", Json.str "outoffuel"),
                      ("detail", Json.str s!"step cap {maxSteps} reached")], s.notes)
  else
    match stepFn m with
    | .next m' =>
      let (s', ev?, risk?, doms') := symStep inputs m m' s
      let acc := match ev? with
        | some ev => acc.push ev.toJson
        | none => acc
      let risks := match risk? with
        | some r => risks.push r.toJson
        | none => risks
      let doms := doms'.foldl (fun (a : Array Json) d => a.push d.toJson) doms
      collect fam inputs (steps + 1) maxSteps acc risks doms s' m'
    | .done v m' =>
      (acc, risks, doms, Json.mkObj [("kind", Json.str "value"),
                        ("detail", Json.str ((RubyCore.inspect m'.heap v).toOption.getD "?")),
                        ("stdout", Json.str m'.out)], s.notes)
    | .uncaught exc m' =>
      let cls := className m'.heap (classOf m'.heap exc)
      let msg := match (m'.heap.get (match exc with | .ref o => o | _ => 0)).payload with
        | .exc s => s
        | _ => ""
      (acc, risks, doms, Json.mkObj [
        ("kind", Json.str (if isTypeError fam m'.heap exc then "typestuck" else "uncaught")),
        ("class", Json.str cls), ("message", Json.str msg),
        ("stdout", Json.str m'.out)], s.notes)
    | .unsupported r =>
      (acc, risks, doms, Json.mkObj [("kind", Json.str "unsupported"), ("detail", Json.str r)], s.notes)
    | .stuck msg =>
      (acc, risks, doms, Json.mkObj [("kind", Json.str "stuck"), ("detail", Json.str msg)], s.notes)

end RubyCore.Concolic

/-- CLI: `rubycore-concolic [maxSteps] [--inputs SPEC] [--bad-state F] < program.json`.
    Inputs are bound to the reserved globals `$__in0`, `$__in1`, … (§6.5), so no
    AST rewriting is needed to supply them.

    `--inputs` accepts two forms:

    * **JSON array** — `--inputs '[31, "Numeric"]'` — the general form, needed now
      that the input vector is heterogeneous (`SymVal`). An element's JSON sort
      *is* its declared sort: that is how the harness author says "this input is a
      string", which is typing information about the program's interface, not a
      hint about the answer.
    * **legacy comma list** — `--inputs 31,7` — all integers. Kept so existing
      callers and tests are unaffected. -/
def parseInputs (args : List String) : List RubyCore.Concolic.SymVal :=
  match args.dropWhile (· != "--inputs") with
  | _ :: spec :: _ =>
    let spec := spec.trimAscii.toString
    if spec.startsWith "[" then
      match Json.parse spec with
      | .ok (.arr elems) => elems.toList.filterMap fun e =>
        match e.getInt? with
        | .ok n => some (.i n)
        | .error _ => match e.getStr? with
          | .ok s => some (.s s)
          | .error _ => none
      | _ => []
    else
      (spec.splitOn ",").filterMap fun t =>
        let t := t.trimAscii
        if t.startsWith "-" then
          (t.drop 1).toString.toNat?.map (fun n => .i (-(Int.ofNat n)))
        else t.toNat?.map (fun n => .i (Int.ofNat n))
  | _ => []

/-- `--bad-state type|type+name` (default `type`). An unrecognized value is a hard
    error rather than a silent fallback: guessing the family would make the verdict
    mean something other than what the caller asked for. -/
def parseFamily (args : List String) : Except String RubyCore.Concolic.BadStateFamily :=
  match args.dropWhile (· != "--bad-state") with
  | _ :: spec :: _ =>
    match RubyCore.Concolic.BadStateFamily.ofString spec.trimAscii.toString with
    | some f => .ok f
    | none => .error s!"unknown --bad-state '{spec}' (expected: type | type+name)"
  | _ => .ok .typeOnly

def main (args : List String) : IO UInt32 := do
  let inputs := parseInputs args
  let fam ← match parseFamily args with
    | .ok f => pure f
    | .error e => IO.eprintln e; return 1
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
      -- Boot the prelude first, exactly as the SUT does (`Prelude.initWithPrelude`).
      -- Without this the tracer runs on a bare heap and silently sees a SMALLER
      -- language than the model it is supposed to be executing.
      match RubyCore.Prelude.initWithPrelude prog with
      | .error e =>
        IO.println (Json.mkObj [("branches", Json.arr #[]),
          ("outcome", Json.mkObj [("kind", Json.str "stuck"),
                                  ("detail", Json.str s!"prelude boot: {e}")])]).compress
        return 0
      | .ok booted =>
      let m0 := RubyCore.Concolic.initMachineOn booted inputs
      let s0 := RubyCore.Concolic.initSym inputs
      let (branches, risks, domains, outcome, notes) :=
        RubyCore.Concolic.collect fam inputs 0 maxSteps #[] #[] #[] s0 m0
      IO.println (Json.mkObj [
        ("branches", Json.arr branches),
        ("dispatchrisks", Json.arr risks),
        ("domains", Json.arr domains),
        ("outcome", outcome),
        ("badstate", Json.str fam.name),
        ("frontier", Json.arr (notes.map Json.str).toArray)]).compress
      return 0
