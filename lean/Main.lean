/-
The difftest SUT executable (lean-model-sketch §4): RubyCore-JSON on stdin →
Observation-JSON on stdout.

Exit codes (mirroring the desugar SUT adapter contract):
  0 — observation printed
  3 — out of modeled fragment; reason on stderr
  1 — harness error (bad input, stuck machine); message on stderr
-/
import RubyCore.Obs
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
  match Lean.Json.parse input with
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
      if let some maxSteps := traceSteps then
        IO.println (Trace.traceJson maxSteps (Machine.init prog)).compress
        return 0
      let result := Interp.run fuel (Machine.init prog)
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
