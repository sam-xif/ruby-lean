import Ratchet.Rung

/-! Small playground adapter: decode one program/Deriv pair and print validateD's Bool. -/

open Ratchet
open Lean (Json)

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match Json.parse input with
  | .error e =>
    IO.eprintln s!"JSON parse error: {e}"
    return 1
  | .ok j =>
    let decoded : Except String (Expr × Deriv) := do
      let p ← Decode.program (← j.getObjVal? "program")
      let d ← Deriv.ofJson? (← j.getObjVal? "deriv")
      return (p, d)
    match decoded with
    | .ok (p, d) =>
      let accepted := validateD p d
      IO.println (Json.compress (Json.mkObj [("validateD", .bool accepted)]))
      return 0
    | .error e =>
      IO.eprintln e
      return 1
