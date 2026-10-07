import Books.TypeSoundness.Rules.Closure.SymbolBody
import Books.TypeSoundness.Conformance.Core.Boot

/-! Native Symbol conversion: real allocation/activation/forwarding and guarded
dispatch. Sorbet 0.6.13405 gives map(&:to_s) Array[String], rejecting an unknown
method (7003) and &:+'s missing argument (7004). No source admission is asserted. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.SymbolClosureControls
open RubyCore Checker Checker.Soundness

example (hb : bootOkB = true) (call : BlockPassCall) (name : String) :
    Interp.coerceBlockPass bootMachine call (.sym name) = .next
      (Interp.withKont (symbolAllocated bootMachine name) (.value (.ref bootMachine.heap.objs.size))
        (.blkConvertK call (.sym name) (.converted true))) :=
  coerceBlockPass_symbol (stateOk_boot hb) rfl call name

example (hb : bootOkB = true) (name : String) (args : List Value) :
    StateOk ctx0 [] .ivar0 (symbolRest (symbolAllocated bootMachine name) args) :=
  symbolRest_state (symbolAllocated_state (stateOk_boot hb) name) args

private def caller : Machine :=
  ((bootMachine.setLocal "__recv" (.int 99)).setLocal "__rest" (.int 88)).setLocal "outer" (.int 77)
private def entered : Machine := symbolEntry caller "+" (.int 2) [.int 3]

#guard (entered.getLocal "__recv").identEq (.int 2)
#guard match (entered.heap.get caller.heap.objs.size).payload with
  | .arr xs => match xs.toList with | [.int n] => n == 3 | _ => false
  | _ => false
#guard (entered.getLocal "__rest").identEq (.ref caller.heap.objs.size)
#guard (entered.getLocal "outer").identEq .nil
#guard entered.currentFrame.captured.isNone
#guard entered.currentFrame.lam
#guard entered.frames.size == caller.frames.size + 1
#guard entered.heap.objs.size == caller.heap.objs.size + 1
#guard match Interp.run 30 (evalFrom entered (symbolBody "+")) with
  | .value v _ => v.identEq (.int 5)
  | _ => false
#guard let m := symbolEntry caller "to_s" (.int 7) []
  match Interp.run 30 (evalFrom m (symbolBody "to_s")) with
  | .value (.ref o) n => match (n.heap.get o).payload with | .str s => s == "7" | _ => false
  | _ => false
-- Lambda semantics preserve an Array receiver as one argument; there is no auto-splat.
#guard let (v, m) := Builtins.allocArr caller #[.int 1, .int 2]
  (symbolEntry m "length" v []).getLocal "__recv" |>.identEq v
#guard Semantics.typeStuck (Interp.run 30
  (evalFrom (symbolEntry caller "+" (.int 2) []) (symbolBody "+")))
#guard Semantics.typeStuck (Interp.run 30
  (evalFrom (symbolEntry caller "missing_symbol_method" (.int 2) []) (symbolBody "missing_symbol_method")))
#guard match Interp.callClosure caller (symbolClosure "to_s") [] none with
  | .next n => Semantics.typeStuck (Interp.run 30 n)
  | _ => false

private def replacement : MethodDef := { params := [], body := .nil, owner := Boot.symbolId }
private def replaced (md : MethodDef) : Heap := defineMethod bootMachine.heap Boot.symbolId "to_proc" md

#guard nativeDispatchB bootMachine.heap (fun _ => true)
-- Neither an override nor a tombstone can supply the native conversion capability.
#guard !nativeDispatchB (replaced replacement) (fun _ => true)
#guard !nativeDispatchB (replaced { replacement with undefined := true }) (fun _ => true)
#guard !nativeDispatchB (replaced { replacement with builtin := some "Proc#to_proc" }) (fun _ => true)
-- Reserving the selector removes the obligation, but also prevents its use by the theorem.
#guard nativeDispatchB (replaced replacement) (fun name => name != "to_proc")

end Checker.Soundness.Typed.SymbolClosureControls
