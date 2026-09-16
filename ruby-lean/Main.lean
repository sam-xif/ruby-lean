/-
The difftest SUT executable (lean-model-sketch §4): RubyCore-JSON on stdin →
Observation-JSON on stdout.

Exit codes (mirroring the desugar SUT adapter contract):
  0 — observation printed
  3 — out of modeled fragment; reason on stderr
  1 — harness error (bad input, stuck machine); message on stderr

Besides running a program, it answers three *static* queries over the same AST —
`--fragment`, `--sigs` and the `--trace`/`--steps` views. The static **type**
queries it used to carry (`--check`, `--check-tl`, `--assn`, `--assn-program`,
`--certify`, `--certify-j`, `--census-j`) were the pre-ratchet type-checking
iterations and were removed with them; the checker of record is `validateD`
(`Ratchet/Check.lean`, `lake exe ratchetd`).
-/
import RubyCore.Obs
import RubyCore.Types.Fragment
import RubyCore.Types.SigRead
import RubyCore.PreludeBoot
import RubyCore.Trace

open RubyCore

def fuelDefault : Nat := 5_000_000
def traceStepsDefault : Nat := 3000

def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let fuel := match args with
    | ["--fuel", n] => n.toNat?.getD fuelDefault
    | _ => fuelDefault
  -- `--trace [N]`: emit the step-by-step config trace (playground) instead of
  -- a single Observation. Decode errors still exit 1; a trace always exits 0
  -- (unsupported/stuck are reported inside the JSON `status`).
  let traceSteps : Option Nat := match args with
    | "--trace" :: rest => some (rest.head?.bind (·.toNat?) |>.getD traceStepsDefault)
    | _ => none
  -- Where the trace window starts. A whole-program trace is only viable for a
  -- toy: the Homebrew slice is ~1.1M steps and a snapshot is ~1 KB, so "from
  -- step 0" shows the first 0.4% of a class-definition boot and nothing anyone
  -- wants to look at. `--trace-from N` skips N steps; `--trace-at SUBSTR` skips
  -- to the first step whose *rendered* control contains SUBSTR (`send .compare(`),
  -- which is the form that works when the step index is not knowable in advance.
  let flagArg : String → Option String := fun name =>
    (args.dropWhile (· != name))[1]?
  let traceStart : Option Trace.Start :=
    match flagArg "--trace-at" with
    | some needle => some (.atCtl needle)
    | none => ((flagArg "--trace-from").bind (·.toNat?)).map .atStep
  -- `--steps`: how many steps the program takes, emitting no snapshots — the
  -- number a window is chosen against.
  let countOnly := args.contains "--steps"
  -- `--fragment`: report whether the program is in the **Sorbet fragment** (the
  -- scope any soundness theorem can have — `RubyCore/Types/Fragment.lean`),
  -- with a reason per exclusion. A static query: nothing is executed, so the
  -- prelude is not booted and the answer is independent of model coverage.
  let fragmentOnly := args.contains "--fragment"
  -- `--sigs`: report the Sorbet signatures the program *declares*, as read off
  -- the AST (`RubyCore/Types/SigRead.lean`). Static, like `--fragment`: reading a
  -- declared type runs nothing, so the answer is independent of model coverage.
  -- It is the signature manifest the ratchet's pipeline reads (stage 1) and the
  -- one difftest's Sorbet harness compares against `srb`.
  let sigsOnly := args.contains "--sigs"
  match Json.parse input with
  | .error e =>
    IO.eprintln s!"bad input JSON: {e}"
    return 1
  | .ok j =>
    match Decode.program j with
    | .error e =>
      -- A deliberate decode-time fragment gate (`UNSUPPORTED: …`, e.g. a v4
      -- param kind or additive head the stepper doesn't model yet) is engine
      -- Unsupported (exit 3), not a model bug. Genuine malformations stay 1.
      if "UNSUPPORTED: ".isPrefixOf e then
        IO.eprintln e
        return 3
      else
        IO.eprintln s!"undecodable RubyCore: {e}"
        return 1
    | .ok prog =>
      if sigsOnly then
        let decls := Types.collectSigs prog
        let paramJson := fun (pn : String) (pt : Types.SigTy) =>
          Json.mkObj [("name", Json.str pn),
                           ("type", Json.str pt.render)]
        let declJson := fun (name : String) (d : Types.SigDecl) =>
          Json.mkObj [
            ("method", Json.str name),
            ("params", Json.arr
              (d.params.map (fun p => paramJson p.1 p.2)).toArray),
            -- `null` is `.void`, which is Sorbet saying "no meaningful return"
            -- — not an absence of information.
            ("returns", match d.ret with
              | some t => Json.str t.render
              | none => Json.null)]
        IO.println (Json.mkObj [
          ("sigs", Json.arr
            (decls.map (fun d => declJson d.1 d.2)).toArray)]).compress
        return 0
      if fragmentOnly then
        let vs := Types.violationSummary prog
        IO.println (Json.mkObj [
          ("in_fragment", Json.bool vs.isEmpty),
          ("violations", Json.arr (vs.map (fun v => Json.mkObj [
            ("kind", Json.str v.kind),
            ("what", Json.str v.what),
            ("reason", Json.str v.reason)])).toArray)]).compress
        return 0
      -- Phase 1: boot the prelude (the core library written in RubyCore, L62);
      -- phase 2 runs `prog` on the resulting heap. A prelude failure is a model
      -- bug, never a program outcome → exit 1.
      let m0 ← match Prelude.initWithPrelude prog with
        | .error e =>
          IO.eprintln s!"MODEL PRELUDE FAILURE (bug): {e}"
          return 1
        | .ok m0 => pure m0
      if countOnly then
        IO.println (Trace.countJson m0).compress
        return 0
      if let some maxSteps := traceSteps then
        IO.println (Trace.traceJson maxSteps m0 traceStart).compress
        return 0
      let result := Interp.run fuel m0
      match observe result with
      | .obs obs =>
        IO.println obs.compress
        return 0
      | .unsupported reason =>
        IO.eprintln reason
        return 3
      | .stuck msg =>
        IO.eprintln s!"MODEL STUCK (bug): {msg}"
        return 1
