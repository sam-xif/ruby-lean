import Denote.Typed.InstanceResolve
import Denote.Sanity

/-! Actual define/call controls. A positive installed row alone does not exclude prepends
or payload interception, and initialize's deliberate privacy must not be bypassed. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def point : Ratchet.Expr := .class' "Point" none (.def' "answer" [] (.int 1))
private def callAnswer : Ratchet.Expr :=
  .send (some (.send (some (.const "Point")) "new" [] none)) "answer" [] none
private def ownOne (m : Machine) (k : ObjId) (name : String) : Bool :=
  ((m.heap.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == name)).map (·.2))).any
    (fun md => instanceMethodCodeB k name md && match md.body with | .int 1 => true | _ => false)

#guard match Interp.run 100 (evalFrom bootMachine point) with
  | .value _ m => match classNamed? m.heap "Point" with
    | some k => classFrontB m.heap k && ownOne m k "answer" &&
        match Interp.run 100 (evalFrom m callAnswer) with
        | .value (.int 1) _ => true
        | _ => false
    | none => false
  | _ => false

private def intercept : Ratchet.Expr := .seq [
  .module' "Interceptor" (.def' "answer" [] .fls),
  .send (some (.const "Point")) "prepend" [.const "Interceptor"] none]

-- The original row is unchanged, but dispatch now runs the prepended body.
#guard match Interp.run 100 (evalFrom bootMachine point) with
  | .value _ m => match classNamed? m.heap "Point" with
    | some k => match Interp.run 100 (evalFrom m intercept) with
      | .value _ n => ownOne n k "answer" && !classFrontB n.heap k &&
          Semantics.typeStuck (Interp.run 100 (evalFrom n
            (.send (some callAnswer) "+" [.int 1] none)))
      | _ => false
    | none => false
  | _ => false

-- initialize is installed correctly, but an explicit call is still private.
#guard Semantics.typeStuck (Interp.run 150 (evalFrom bootMachine (.seq [
  .class' "Point" none (.def' "initialize" [] .nil),
  .send (some (.send (some (.const "Point")) "new" [] none)) "initialize" [] none])))

-- Heap countermodel, not Ruby source: changing only the receiver payload leaves its
-- nominal type and installed method intact, but Proc#call interception runs a different body.
#guard match Interp.run 100 (evalFrom bootMachine
    (.class' "Point" none (.def' "call" [] (.int 1)))) with
  | .value _ m => match Interp.run 100 (evalFrom m (.send (some (.const "Point")) "new" [] none)) with
    | .value (.ref o) n => match classNamed? n.heap "Point" with
      | some k =>
          let n := n.setLocal "obj" (.ref o)
          let expr : Ratchet.Expr := .send (some (.var .lvar "obj")) "call" [] none
          let obj := n.heap.get o
          let closure : Closure := {
            params := [], locals := [], body := .fls
            captured := none, home := n.stack.headD 0, lam := true }
          let bad := { n with heap := n.heap.set o { obj with payload := .proc closure } }
          ownOne bad k "call" && classFrontB bad.heap k && isExactInst bad.heap (.ref o) "Point" &&
            (match Interp.run 100 (evalFrom n expr) with | .value (.int 1) _ => true | _ => false) &&
            Semantics.typeStuck (Interp.run 100 (evalFrom bad (.send (some expr) "+" [.int 1] none)))
      | none => false
    | _ => false
  | _ => false

end Ratchet.Denote.Typed
