import RubyCore.Interp

/-! A kernel-checked obstruction to repairing every proof without changing any
theorem statement. `KontFrame.lean` does not build, so the two definitions below
are copied from it instead of importing its failed proofs. The negated statement
is exactly `RubyCore.Proof.callClosure_frame` with those definitions.

An appended block-call marker revives the closure's saved break scope. Framing
the result of the original call only appends the marker and cannot change the
break target already recorded in the block activation. -/
namespace RubyCore.Proof.StatementObstruction

-- These are the definitions in the currently broken KontFrame.lean.
def pushK (K : List Kont) (m : Machine) : Machine :=
  { m with kont := m.kont ++ K }

def frameR (K : List Kont) : StepResult → StepResult
  | .next m => .next (pushK K m)
  | r => r

def scopedClosure : Closure :=
  { params := [], locals := [], body := .nil, captured := none,
    home := 0, breakScope := some 7 }

def nextBreakScope : StepResult → Option FrameId
  | .next m => match m.kont with
    | .blkFrameK _ _ brk _ _ :: _ => brk
    | _ => none
  | _ => none

theorem framed_scope :
    nextBreakScope (Interp.callClosure
      (pushK [.blockCallK 7] default) scopedClosure [] none none none) = some 7 := rfl

theorem unframed_scope :
    nextBreakScope (frameR [.blockCallK 7]
      (Interp.callClosure default scopedClosure [] none none none)) = none := rfl

-- The exact universal statement of KontFrame.callClosure_frame is false.
theorem not_callClosure_frame : ¬ (∀ (K : List Kont) (m : Machine) (cl : Closure)
    (args : List Value) (brk : Option FrameId) (selfOv : Option Value)
    (defmodOv : Option ObjId),
    Interp.callClosure (pushK K m) cl args brk selfOv defmodOv =
      frameR K (Interp.callClosure m cl args brk selfOv defmodOv)) := by
  intro h
  have bad := congrArg nextBreakScope
    (h [.blockCallK 7] default scopedClosure [] none none none)
  change some 7 = (none : Option FrameId) at bad
  cases bad

#print axioms not_callClosure_frame

end RubyCore.Proof.StatementObstruction
