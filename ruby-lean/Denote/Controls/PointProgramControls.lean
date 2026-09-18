import Denote.Examples.PointProgram
import Denote.Sem.Core.Boot

/-! Full class/constructor/getter executions complement the annotation-domain proof. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.PointClass
open RubyCore Ratchet Ratchet.Denote

#guard (constOwn bootMachine.heap Boot.objectId "Point").isNone
#guard match Interp.run 300 (evalFrom bootMachine (fullProgram 1 2)) with
  | .value (.int 1) _ => true
  | _ => false

-- Both method activations must restore the caller's differently typed x.
#guard match Interp.run 350 (evalFrom bootMachine (.seq [
    .vasgn .lvar "x" (.str "caller"), fullProgram 3 4,
    .send (some (.var .lvar "x")) "length" [] none])) with
  | .value (.int 6) _ => true
  | _ => false

end Ratchet.Denote.Typed.PointClass
