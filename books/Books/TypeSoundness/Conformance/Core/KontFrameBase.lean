import Books.Metatheory.Framing.RootFrameContext

/-! Continuation framing definitions used by run decomposition. These need only
interpreter framing, independently of type-conformance transport. Frame.lean
re-exports them for the typing layer. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore

/-- The continuation tail, appended. -/
def pushK (K : List Kont) (m : Machine) : Machine := { m with kont := m.kont ++ K }

/-- A step result, with the tail carried through. -/
def frameR (K : List Kont) : StepResult → StepResult
  | .next m => .next (pushK K m)
  | r => r

/-- Compatibility name for the remaining continuation observation: catch tags. -/
abbrev CatchFree (K : List Kont) : Prop := RubyCore.Proof.Root.ContextFree K

/-- The current interpreter frame rule follows saved root executions through
Enumerator suspension. Its proof is `Decompose.kontFrameCatchFree`; the name is
retained for compatibility, but ContextFree covers every observed frame kind. -/
def KontFrameCatchFree : Prop :=
  ∀ (m : Machine) (K : List Kont), CatchFree K →
    (m.kont ≠ [] ∨ ∃ e, m.ctl = .eval e) →
    Interp.stepFn (Proof.pushRootK K m) = Proof.rootFrameR K (Interp.stepFn m)

end Checker.Soundness
