/- Test-only entry point for check-require-relative.py; not a runtime file loader.

   Boots the prelude (which mounts the VFS library fixture), gives the top-level
   program the source path the harness assigns it, and runs it. The libraries it
   `require_relative`s come from the boot fixture, not from this input. -/
import RubyCore.Boot
import RubyCore.Obs
open RubyCore

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let parsed : Except String (Expr × String) := do
    let j ← Json.parse input
    let program ← Decode.program (← j.getObjVal? "program")
    let path ← (← j.getObjVal? "path").getStr?
    return (program, path)
  match parsed with
  | .error e => throw (IO.userError e)
  | .ok (program, path) =>
    match Prelude.initWithPrelude program with
    | .error e => throw (IO.userError e)
    | .ok m =>
      -- Give the top-level frame (index 0) the program's own path, so
      -- `require_relative` from the program resolves against its directory.
      let top := m.frames.getD 0 default
      let m := { m with frames := m.frames.set! 0 { top with sourcePath := some path } }
      match observe (Interp.run 100000 m) 100000 with
      | .obs j => IO.println j.compress
      | .unsupported e => throw (IO.userError e)
      | .stuck e => throw (IO.userError e)
