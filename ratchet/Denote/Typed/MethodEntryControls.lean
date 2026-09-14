import Denote.Typed.MethodEntry

/-! Runtime controls for the real call boundary, and a caller-framing counterexample.
None of these is counted as checker method coverage. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def caller : Machine := (Machine.init .nil).setLocal "outer" (.int 9)
private def addMethod : MethodDef :=
  { params := [.req "x", .req "y"], owner := Boot.objectId,
    body := toRuby (.send (some (.var .lvar "x")) "+" [.var .lvar "y"] none) }
private def enterAdd (args : List Value) : StepResult :=
  Interp.enterUserMethod caller caller.currentFrame.self "add" addMethod args none

-- Correct parameters, a fresh local environment, and return to the original frame.
#guard match enterAdd [.int 1, .int 2] with
  | .next n =>
    Value.identEq (n.getLocal "x") (.int 1) && Value.identEq (n.getLocal "y") (.int 2) &&
    Value.identEq (n.getLocal "outer") .nil &&
    match Interp.run 40 n with
    | .value (.int 3) result => result.stack == caller.stack &&
        Value.identEq (result.getLocal "outer") (.int 9)
    | _ => false
  | _ => false

-- Both missing and surplus arguments really take the ArgumentError path.
#guard ([[], [.int 1], [.int 1, .int 2, .int 3]] : List (List Value)).all fun args =>
  match enterAdd args with
  | .next n => match n.ctl with
    | .jump (.raiseJ exc) => Semantics.isTypeError n.heap exc
    | _ => false
  | _ => false

#guard match Interp.enterUserMethod caller caller.currentFrame.self "zero"
    { addMethod with params := [], body := .int 7 } [] none with
  | .next n => match Interp.run 5 n with
    | .value (.int 7) result => result.stack == caller.stack
    | _ => false
  | _ => false

example : EnvOk [("x", .int), ("y", .int)]
    (pushMethodFrame caller
      (requiredFrame caller.currentFrame.self "add" addMethod ["x", "y"] [.int 1, .int 2])) :=
  requiredFrame_envOk caller _ "add" addMethod _ _ rfl
    (by simp [DenAll, denM, isIntV]) (by simp [FirstOrder, isAliasTy])

-- Framed alone does NOT protect the inactive caller's locals. The damaged state is
-- not claimed reachable: it refutes a proposed transport from this contract alone.
private def entered : Machine :=
  pushMethodFrame caller (requiredFrame caller.currentFrame.self "add" addMethod [] [])
private def damaged : Machine :=
  let badFrame := { caller.currentFrame with locals := [("outer", .bool true)] }
  { entered with frames := entered.frames.set! 0 badFrame }

theorem framed_does_not_protect_caller :
    Framed entered damaged ∧
      ¬ EnvOk [("outer", .int)] { damaged with stack := damaged.stack.tail } := by
  refine ⟨Framed.of_heap_stack rfl rfl, ?_⟩
  intro h
  have hd := (h.1 "outer" .int rfl).1
  change denM .int _ (.bool true) at hd
  simp [denM, isIntV] at hd

#print axioms framed_does_not_protect_caller
end Ratchet.Denote.Typed
