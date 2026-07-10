/-
The difftest SUT executable (lean-model-sketch §4): RubyCore-JSON on stdin →
Observation-JSON on stdout.

Exit codes (mirroring the desugar SUT adapter contract):
  0 — observation printed
  3 — out of modeled fragment; reason on stderr
  1 — harness error (bad input, stuck machine); message on stderr
-/
import RubyCore.Obs

open RubyCore

def fuelDefault : Nat := 5_000_000

def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let fuel := match args with
    | ["--fuel", n] => n.toNat?.getD fuelDefault
    | _ => fuelDefault
  match Lean.Json.parse input with
  | .error e =>
    IO.eprintln s!"bad input JSON: {e}"
    return 1
  | .ok j =>
    match Decode.program j with
    | .error e =>
      IO.eprintln s!"undecodable RubyCore: {e}"
      return 1
    | .ok prog =>
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
