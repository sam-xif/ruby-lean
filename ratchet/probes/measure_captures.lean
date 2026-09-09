/- Run with `lake env lean probes/measure_captures.lean` from `ruby/ratchet`.

   The two measurements behind `Denote/Sem/notes.md`'s eighteenth stall point:
   how much of `Sealed`'s closure clause, and of the proposed `MethodDef` arm, is
   non-vacuous at the machine the ladder starts from.

   Answers, 2026-09-08: **0 and 0**. 71 frames survive the boot (dead activations
   still in the array) but the stack is `[0]`.
-/
import Denote.Sanity

set_option autoImplicit false
open RubyCore Ratchet.Denote

/-- Every method installed anywhere in the heap that carries a `capturedFrame`. -/
def capturedMethods (m : Machine) : List (ObjId × String × Nat) :=
  (List.range m.heap.objs.size).flatMap fun k =>
    match m.heap.classPayload? k with
    | some cp => cp.methods.filterMap fun p =>
        match p.2.capturedFrame with
        | some f => some (k, p.1, f)
        | none => none
    | none => []

/-- …and every Proc object in the heap, with the frame it captured. -/
def heapProcs (m : Machine) : List (ObjId × Nat) :=
  (List.range m.heap.objs.size).filterMap fun o =>
    match (m.heap.get o).payload with
    | .proc cl => some (o, cl.captured)
    | _ => none

#eval (capturedMethods bootMachine).length   -- 0
#eval (heapProcs bootMachine).length         -- 0
#eval bootMachine.frames.size                -- 71
#eval bootMachine.stack                      -- [0]
