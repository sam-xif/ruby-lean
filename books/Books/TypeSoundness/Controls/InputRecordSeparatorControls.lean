import Books.TypeSoundness.Conformance.Core.Boot

/-! Runtime controls for the global input record separator `$/` in `IO#gets`
(issue #64). The boot fixture `/tmp/vfsdata/nums.txt` holds `"1\n2\n3\n"`.
`/` is read at call time: unset means newline, `nil` reads to EOF, a String is
an arbitrary separator, and the two shapes the model does not approximate —
paragraph mode (`$/ = ""`) and a non-String, non-nil separator — gate by name. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.InputRecordSeparatorControls
open RubyCore Checker Checker.Soundness

private def openNums : Checker.Expr :=
  .send (some (.const "File")) "open" [.str "/tmp/vfsdata/nums.txt"] none

private def gets : Checker.Expr :=
  .send (some (.var .lvar "f")) "gets" [] none

/-- Open the fixture, run `setup` (usually a `$/` assignment), then `n` gets
calls; the program's value is the last call's. -/
private def runGets (setup : Checker.Expr) (n : Nat) : Interp.RunResult :=
  Interp.run 2000 (evalFrom bootMachine
    (.seq ([.vasgn .lvar "f" openNums, setup] ++ List.replicate n gets)))

private def lineOf : Interp.RunResult → Option String
  | .value v m => Builtins.strPayload? m.heap v
  | _ => none

-- Unset `$/` is CRuby's `"\n"`.
#guard lineOf (runGets .nil 1) == some "1\n"

-- A multi-character separator runs through its first occurrence.
#guard lineOf (runGets (.vasgn .gvar "$/" (.str "2")) 1) == some "1\n2"

-- After the separator, the remainder (no second `2`) is the rest of the file.
#guard lineOf (runGets (.vasgn .gvar "$/" (.str "2")) 2) == some "\n3\n"

-- `$/ = nil` reads to end of file.
#guard lineOf (runGets (.vasgn .gvar "$/" .nil) 1) == some "1\n2\n3\n"

-- Paragraph mode is gated rather than approximated.
#guard match runGets (.vasgn .gvar "$/" (.str "")) 1 with
  | .unsupported reason _ => reason == "IO#gets: paragraph mode (an empty record separator) is not modelled"
  | _ => false

-- A non-String, non-nil separator would raise TypeError in CRuby; gate it.
#guard match runGets (.vasgn .gvar "$/" (.int 1)) 1 with
  | .unsupported reason _ => reason == "IO#gets: argument shape outside step 5"
  | _ => false

end Checker.Soundness.Typed.InputRecordSeparatorControls
