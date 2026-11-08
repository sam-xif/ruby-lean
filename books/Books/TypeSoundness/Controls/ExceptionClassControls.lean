import Books.TypeSoundness.Conformance.Core.Boot

/-! The boot exception vocabulary: `IOError` and `EOFError` are real constants
with CRuby's ancestry, and a program can raise and rescue them (issue #37 step 7). -/
set_option autoImplicit false
namespace Checker.Soundness.ExceptionClassControls
open RubyCore Checker Checker.Soundness

#guard (classNamed? bootMachine.heap "IOError") == some Boot.ioErrorId
#guard (classNamed? bootMachine.heap "EOFError") == some Boot.eofErrorId
#guard (ancestors bootMachine.heap Boot.ioErrorId).contains Boot.standardErrorId
#guard (ancestors bootMachine.heap Boot.eofErrorId).contains Boot.ioErrorId
#guard (ancestors bootMachine.heap Boot.eofErrorId).contains Boot.standardErrorId
#guard !(ancestors bootMachine.heap Boot.eofErrorId).contains Boot.runtimeErrorId

def raiseEOF : Checker.Expr :=
  .send none "raise" [.const "EOFError", .str "end of input"] none

#guard match Interp.run 400 (evalFrom bootMachine raiseEOF) with
  | .uncaught exc m => isA m.heap exc Boot.eofErrorId && !Semantics.isTypeError m.heap exc
  | _ => false

end Checker.Soundness.ExceptionClassControls
