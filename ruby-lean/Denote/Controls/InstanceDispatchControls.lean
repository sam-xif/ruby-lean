import Denote.Rules.Instance.InstanceDispatch
import Denote.Sem.Core.Boot

/-! Name-based dispatch works without empty payloads; sensitive names must still refuse
that route. The receiver class here is independent of the Point program. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

#guard directSendNameB "getX"
#guard directSendNameB "answer"
#guard !directSendNameB "call"
#guard !directSendNameB "[]"
#guard !directSendNameB "new"
#guard !directSendNameB "sqrt"
#guard !directSendNameB "escape"

private def record : Ratchet.Expr := .class' "Record" none (.seq [
  .def' "answer" [] (.int 1), .def' "call" [] (.int 1)])

-- Keep the class, methods and nominal type; change only the receiver to a Proc payload.
-- answer still runs the installed body, while call is intercepted by the false closure.
#guard match Interp.run 100 (evalFrom bootMachine record) with
  | .value _ m => match Interp.run 100 (evalFrom m
      (.send (some (.const "Record")) "new" [] none)) with
    | .value (.ref o) n =>
        let cl : Closure := {
          params := [], locals := [], body := .fls
          captured := none, home := n.stack.headD 0, lam := true }
        let obj := n.heap.get o
        let altered := { n with heap := n.heap.set o { obj with payload := .proc cl } }
        let altered := altered.setLocal "obj" (.ref o)
        isExactInst altered.heap (.ref o) "Record" &&
          (match Interp.run 30 (evalFrom altered (.send (some (.var .lvar "obj")) "answer" [] none)) with
            | .value (.int 1) _ => true
            | _ => false) &&
          (match Interp.run 30 (evalFrom altered (.send (some (.var .lvar "obj")) "call" [] none)) with
            | .value (.bool false) _ => true
            | _ => false)
    | _ => false
  | _ => false

end Ratchet.Denote.Typed
