import Denote.Rules.Primitive.Primitive

/-! Regression controls for the heap assumptions the primitive proof forced. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def malformedString (h : Heap) : Heap := pushHeap h { klass := Boot.stringId }

/-- Nominal membership without a payload is no longer a conformant heap. -/
theorem malformedString_rejected (h : Heap) : ¬ StringPayloadOk (malformedString h) := by
  intro hp
  obtain ⟨s, hs⟩ := hp h.objs.size (by simp [malformedString, classOf, pushHeap_get_self])
  simp [malformedString, pushHeap_get_self] at hs

private def malformedMachine : Machine :=
  ({ bootMachine with heap := malformedString bootMachine.heap }).setLocal "x"
    (.ref bootMachine.heap.objs.size)

-- This was typed and StateOk before StringPayloadOk: the model really raises TypeError.
#guard !stringPayloadB malformedMachine.heap
#guard Semantics.typeStuck (Interp.run 100 (evalFrom malformedMachine
  (.send (some (.str "a")) "+" [.var .lvar "x"] none)))

-- The division row covers its exceptional path, not just its successful corpus example.
example (hb : bootOkB = true) : StuckFree bootMachine
    (.send (some (.int 1)) "/" [.int 0] none) :=
  (SemA.prim SemA.intLit (.cons SemA.intLit .nil rfl) .intDiv).closed (stateOk_boot hb)

#guard match Interp.run 100 (evalFrom bootMachine
    (.send (some (.int 1)) "/" [.int 0] none)) with
  | .uncaught exc m => !Semantics.isTypeError m.heap exc
  | _ => false

#guard !plainArgB (.splat (some (.array [])))
#guard !plainArgB (.kwargs [])
#guard !plainArgB .fwd

-- Both signs, equality and values beyond machine-word range use real Integer dispatch.
example (hb : bootOkB = true) (x y : Int) : StuckFree bootMachine
    (.send (some (.int x)) ">" [.int y] none) :=
  (SemA.prim SemA.intLit (.cons SemA.intLit .nil rfl) .intGt).closed (stateOk_boot hb)

#guard ([(-2, -1, false), (-1, -2, true), (0, 0, false),
    (1000000000000000000000000, 999999999999999999999999, true)] : List (Int × Int × Bool)).all
  fun (x, y, expected) => match Interp.run 100 (evalFrom bootMachine
    (.send (some (.int x)) ">" [.int y] none)) with
  | .value (.bool b) _ => b == expected
  | _ => false

-- Receiver evaluation precedes argument evaluation; both writes reach the caller.
#guard match Interp.run 100 (evalFrom bootMachine
    (.send (some (.vasgn .lvar "x" (.int 2))) ">" [.vasgn .lvar "x" (.int 1)] none)) with
  | .value (.bool true) m => match m.getLocal "x" with
    | .int 1 => true
    | _ => false
  | _ => false

private def replacedGreaterThan : Machine :=
  let h := defineMethod bootMachine.heap Boot.integerId ">"
    { owner := Boot.integerId, params := [.req "other"], body := .nil }
  { bootMachine with heap := h }

-- A well-shaped user method cannot substitute for the certified builtin.
#guard !primitiveDispatchB replacedGreaterThan.heap (nameFreeN ctx0)
#guard match Interp.run 100 (evalFrom replacedGreaterThan
    (.send (some (.int 1)) ">" [.int 0] none)) with
  | .value .nil _ => true
  | _ => false

#print axioms malformedString_rejected
end Ratchet.Denote.Typed
