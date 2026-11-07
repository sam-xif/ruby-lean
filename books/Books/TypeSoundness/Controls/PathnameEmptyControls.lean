import Books.TypeSoundness.Conformance.Core.Boot

/-! Runtime controls for `Pathname#empty?` (issue #91). It asks the filesystem
whether the file is empty, not whether the path String is empty. The boot
fixture `/tmp/readme.txt` holds `"hello\n"`; the model answers the file and
missing-path cases and gates directory emptiness, which needs a directory
listing it does not have. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.PathnameEmptyControls
open RubyCore Checker Checker.Soundness

private def writeToReadme (data : String) : Checker.Expr :=
  .send (some (.const "File")) "write" [.str "/tmp/readme.txt", .str data] none

private def pathnameEmpty (path : String) : Checker.Expr :=
  .send (some (.send (some (.const "Pathname")) "new" [.str path] none)) "empty?" [] none

private def runAfter (setup : Checker.Expr) (path : String) : Interp.RunResult :=
  Interp.run 2000 (evalFrom bootMachine (.seq [setup, pathnameEmpty path]))

private def boolOf : Interp.RunResult → Option Bool
  | .value (.bool b) _ => some b
  | _ => none

-- A non-empty file is not empty.
#guard boolOf (runAfter .nil "/tmp/readme.txt") == some false

-- An empty file is empty, even though its path String is not.
#guard boolOf (runAfter (writeToReadme "") "/tmp/readme.txt") == some true

-- The empty path is not an empty file; CRuby answers false.
#guard boolOf (runAfter .nil "") == some false

-- A missing path answers false rather than raising.
#guard boolOf (runAfter .nil "/tmp/nope") == some false

-- Directory emptiness needs a listing the model does not have: gate it.
#guard match runAfter .nil "/tmp/vfsdata" with
  | .unsupported reason _ => reason == "Pathname#empty? on a directory (directory emptiness is not modelled)"
  | _ => false

end Checker.Soundness.Typed.PathnameEmptyControls
