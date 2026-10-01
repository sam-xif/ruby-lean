import Denote.Examples.ScalarWriteDerivations
import Ratchet.Controls.ScalarWriteControls

/-! Runtime controls and the Boolean counterexample to unrestricted same-type writes. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ScalarWriteControls
open RubyCore Ratchet Ratchet.Denote

theorem bool_write_not_framed {m : Machine} {o : ObjId} {x : String}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size)
    (hx : ivarOf m.heap (.ref o) x = .bool true)
    (ht : isAName m.heap (.bool true) "TrueClass" = true)
    (hf : isAName m.heap (.bool false) "TrueClass" = false) :
    ¬ Framed m (Interp.bindIvar m x (.bool false)) := by
  intro h
  have hold : denM (.cls "TrueClass") m (ivarOf m.heap (.ref o) x) := by
    simpa only [hx, denM] using ht
  have hnew := h.fields.typed o ho x (.cls "TrueClass") rfl hold
  rw [ivarOf_bindIvar_self hs ho, denM, bindIvar_isAName, hf] at hnew
  cases hnew

#guard isAName bootMachine.heap (.bool true) "TrueClass"
#guard !isAName bootMachine.heap (.bool false) "TrueClass"
#guard !scalarWriteB .bool

#guard match Interp.run 500 (evalFrom bootMachine Ratchet.ScalarWriteControls.aliases) with
  | .value (.int 9) _ => true
  | _ => false

-- Freeze is not claimed as a checker rule. The write proof nevertheless covers a frozen
-- receiver and must retain this real non-type-error outcome.
def frozenProgram : Ratchet.Expr := .seq [ScalarWriteProgram.declaration,
  .vasgn .lvar "box" (ScalarWriteProgram.newExpr 1),
  .send (some (.var .lvar "box")) "freeze" [] none,
  .send (some (.var .lvar "box")) "grow" [] none]
#guard match Interp.run 400 (evalFrom bootMachine frozenProgram) with
  | .uncaught exc m => isA m.heap exc Boot.frozenErrorId && !Semantics.isTypeError m.heap exc
  | _ => false
#guard primitiveErrorB bootMachine.heap Boot.frozenErrorId
#print axioms bool_write_not_framed
end Ratchet.Denote.Typed.ScalarWriteControls
