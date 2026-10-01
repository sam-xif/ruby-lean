import Denote.Rules.Iterator.Each
import Denote.Sem.Core.Boot

/-! The loop cursor addresses the live payload, including a replacement, append or
removal since the previous yield. Exhaustion returns the receiver and pops the iterator. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.IteratorEachControls
open RubyCore Ratchet Ratchet.Denote

private def arrayId : ObjId := bootMachine.heap.objs.size
private def caller : Machine := (Builtins.allocArr bootMachine #[.int 1, .int 2]).2
private def active : Machine := pushMethodFrame caller
  { self := .ref arrayId, defmod := Boot.arrayId, kind := .method, meth := "each",
    cref := caller.currentFrame.cref }
private def closure : Closure :=
  { params := [.req "item"], locals := [], body := .var .lvar "item",
    captured := some (caller.stack.headD 0), home := Interp.returnTarget caller, lam := false }
private def changed (xs : Array Value) : Machine :=
  { active with heap := active.heap.set arrayId { active.heap.get arrayId with payload := .arr xs } }

#guard match eachArrayStep (changed #[.int 1, .int 7, .int 3]) closure caller.frames.size arrayId 1 with
  | .next n => (n.getLocal "item").identEq (.int 7)
  | _ => false
#guard match eachArrayStep (changed #[.int 1, .int 7, .int 3]) closure caller.frames.size arrayId 2 with
  | .next n => (n.getLocal "item").identEq (.int 3)
  | _ => false
#guard match eachArrayStep (changed #[.int 1]) closure caller.frames.size arrayId 1 with
  | .next n => match Interp.run 5 n with
    | .value v out => v.identEq (.ref arrayId) && out.stack == caller.stack
    | _ => false
  | _ => false

end Ratchet.Denote.Typed.IteratorEachControls
