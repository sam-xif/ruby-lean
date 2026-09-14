import Denote.Typed.Primitive

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

#print axioms malformedString_rejected
end Ratchet.Denote.Typed
