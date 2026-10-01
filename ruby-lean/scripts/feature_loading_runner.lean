/- Test-only entry point for check-feature-loading.py; not a runtime file loader. -/
import RubyCore.PreludeBoot
import RubyCore.Obs
open RubyCore

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let parsed : Except String (Expr × Expr) := do
    let j ← Json.parse input
    let feature ← Decode.program (← j.getObjVal? "feature")
    let program ← Decode.program (← j.getObjVal? "program")
    return (feature, program)
  match parsed with
  | .error e => throw (IO.userError e)
  | .ok (feature, program) =>
    match Prelude.initWithPrelude program with
    | .error e => throw (IO.userError e)
    | .ok m =>
      let m := { m with featurePrograms := ("loader-spec", feature) :: m.featurePrograms }
      match observe (Interp.run 100000 m) 100000 with
      | .obs j => IO.println j.compress
      | .unsupported e => throw (IO.userError e)
      | .stuck e => throw (IO.userError e)
