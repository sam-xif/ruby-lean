import Denote.Typed.MethodReturn

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

-- Equal heaps/stacks alone do NOT protect the inactive caller's locals. The damaged
-- state is not claimed reachable; the strengthened Framed now excludes this witness.
private def entered : Machine :=
  pushMethodFrame caller (requiredFrame caller.currentFrame.self "add" addMethod [] [])
private def damaged : Machine :=
  let badFrame := { caller.currentFrame with locals := [("outer", .bool true)] }
  { entered with frames := entered.frames.set! 0 badFrame }

theorem heap_stack_does_not_protect_caller :
    damaged.heap = entered.heap ∧ damaged.stack = entered.stack ∧
      ¬ EnvOk [("outer", .int)] { damaged with stack := damaged.stack.tail } := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  have hd := (h.1 "outer" .int rfl).1
  change denM .int _ (.bool true) at hd
  simp [denM, isIntV] at hd

theorem framed_excludes_caller_damage : ¬ Framed entered damaged := by
  intro h
  have hf := h.frames.isolated rfl 0 (by decide) (by decide)
  have hv := congrArg (fun f => (f.locals.find? (·.1 == "outer")).map (·.2)) hf
  change some (Value.bool true) = some (Value.int 9) at hv
  cases hv

private theorem caller_env : EnvOk [("outer", .int)] caller := by
  constructor
  · intro x τ hx
    have hx' : "outer" = x ∧ Ty.int = τ := by simpa [envGet?] using hx
    rcases hx' with ⟨rfl, rfl⟩
    constructor
    · unfold caller
      rw [getLocal_setLocal_self _ _ _ (by decide)]
      simp [stripAlias, denM, isIntV]
    · intro y ρ h; cases h
  · intro x hx
    have hn : x ≠ "outer" := by
      intro he
      subst x
      simp [envGet?] at hx
    unfold caller
    rw [getLocal_setLocal_ne _ _ _ hn]
    rfl

-- A same-named local written inside the uncaptured method leaves the caller typed.
example : EnvOk [("outer", .int)] (popMethodFrame (entered.setLocal "outer" (.bool true))) :=
  method_pop_envOk (m := caller)
    (f := requiredFrame caller.currentFrame.self "add" addMethod [] [])
    (by decide) rfl rfl (Framed_setLocal entered "outer" (.bool true))
    caller_env (by simp [stripAlias, FirstOrder])

-- Captured activations may write the caller; FramePres deliberately does not deny this.
private def capturedEntry : Machine :=
  pushMethodFrame caller
    { requiredFrame caller.currentFrame.self "dm" addMethod [] [] with captured := some 0 }
#guard Value.identEq
  ((popMethodFrame (capturedEntry.setLocal "outer" (.bool true))).getLocal "outer") (.bool true)
example : FramePres capturedEntry (capturedEntry.setLocal "outer" (.bool true)) :=
  .setLocal _ _ _

#print axioms heap_stack_does_not_protect_caller
#print axioms framed_excludes_caller_damage
end Ratchet.Denote.Typed
