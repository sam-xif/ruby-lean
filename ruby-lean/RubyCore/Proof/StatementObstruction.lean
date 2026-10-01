import RubyCore.Interp

/-! Historical obstruction and its dynamic-state repair. The legacy helper below
reconstructs break liveness from kont as the interpreter did before liveBreakScopes.

An appended block-call marker revives the closure's saved break scope. Framing
the result of the original call only appends the marker and cannot change the
break target already recorded in the block activation. -/
namespace RubyCore.Proof.StatementObstruction

-- The old stack-only framing action, retained for the historical counterexample.
def pushK (K : List Kont) (m : Machine) : Machine :=
  { m with kont := m.kont ++ K }

def frameR (K : List Kont) : StepResult → StepResult
  | .next m => .next (pushK K m)
  | r => r

def scopedClosure : Closure :=
  { params := [], locals := [], body := .nil, captured := none,
    home := 0, breakScope := some 7 }

def legacyCallClosure (m : Machine) (cl : Closure) (args : List Value)
    (brk : Option FrameId) (selfOv : Option Value) (defmodOv : Option ObjId) : StepResult :=
  Interp.callClosure { m with liveBreakScopes := m.kont.filterMap fun k => match k with
    | .blockCallK scope => some scope | _ => none } cl args brk selfOv defmodOv

def nextBreakScope : StepResult → Option FrameId
  | .next m => match m.kont with
    | .blkFrameK _ _ brk _ _ :: _ => brk
    | _ => none
  | _ => none

theorem framed_scope :
    nextBreakScope (legacyCallClosure
      (pushK [.blockCallK 7] default) scopedClosure [] none none none) = some 7 := rfl

theorem unframed_scope :
    nextBreakScope (frameR [.blockCallK 7]
      (legacyCallClosure default scopedClosure [] none none none)) = none := rfl

-- The old universal statement was false for the stack-probing interpreter.
theorem not_legacy_callClosure_frame : ¬ (∀ (K : List Kont) (m : Machine) (cl : Closure)
    (args : List Value) (brk : Option FrameId) (selfOv : Option Value)
    (defmodOv : Option ObjId),
    legacyCallClosure (pushK K m) cl args brk selfOv defmodOv =
      frameR K (legacyCallClosure m cl args brk selfOv defmodOv)) := by
  intro h
  have bad := congrArg nextBreakScope
    (h [.blockCallK 7] default scopedClosure [] none none none)
  change some 7 = (none : Option FrameId) at bad
  cases bad

/-- An appended marker cannot revive a dead token in the repaired interpreter. -/
theorem marker_does_not_revive :
    nextBreakScope (Interp.callClosure
      (pushK [.blockCallK 7] default) scopedClosure [] none none none) = none := rfl

/-- A detached continuation does not kill a token inherited in execution state. -/
theorem detached_scope_live :
    nextBreakScope (Interp.callClosure
      { (default : Machine) with liveBreakScopes := [7] }
      scopedClosure [] none none none) = some 7 := rfl

#print axioms not_legacy_callClosure_frame

end RubyCore.Proof.StatementObstruction
