import Denote.Examples.PointConstructorExpr
import Denote.Sem.Core.Boot

/-! The full class/new expression, including argument effects and retained caller locals.
The method body remains the single annotation-domain initializer proof. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.PointClass
open RubyCore Ratchet Ratchet.Denote

def effectfulNew : Ratchet.Expr := .send (some (.const "Point")) "new"
  [.vasgn .lvar "a" (.int 3), .var .lvar "a"] none

theorem argument_effects_sem : SemSafeCtxA callerCtx [] .ivar0 effectfulNew
    (.inst "Point" pointInitSpine) callerCtx [("a", .int)] .ivar0 :=
  constructor_expr const_point
    (.cons (SemSafeCtxA.intLit.vasgn rfl rfl (by decide))
      (.cons (SemSafeCtxA.var rfl rfl) .nil rfl) rfl) rfl rfl (by simp [FirstOrder, stripAlias])

theorem class_argument_effects_run (hb : bootOkB = true) :
    RunSpec bootMachine (evalFrom bootMachine (.seq [program, effectfulNew]))
      [("a", .int)] (.inst "Point" pointInitSpine) callerCtx .ivar0 :=
  (runSpec (stateOk_boot hb) rfl (by simp)).thenSeq (.last argument_effects_sem)

-- Argument allocation must retain the already evaluated class receiver's identity/type.
theorem allocating_args_sem (x y : Int) : SemSafeCtxA callerCtx [] .ivar0
    (.send (some (.const "Point")) "new" [.seq [.str "scratch", .int x], .int y] none)
    (.inst "Point" pointInitSpine) callerCtx [] .ivar0 :=
  constructor_expr const_point
    (.cons (SemSafeCtxA.strLit.seq .intLit) (.cons .intLit .nil rfl) rfl) rfl rfl (by simp)

-- A literal construction returns both annotated fields, never initialize's Integer result.
#guard match Interp.run 300 (evalFrom bootMachine (.seq [program, newExpr 4 7])) with
  | .value (.ref o) n =>
      isExactInst n.heap (.ref o) "Point" &&
      (match (n.heap.get o).ivars.lookup "@x", (n.heap.get o).ivars.lookup "@y" with
        | some (.int 4), some (.int 7) => true
        | _, _ => false)
  | _ => false

-- The second argument reads the first one's assignment; the caller keeps that local.
#guard match Interp.run 300 (evalFrom bootMachine (.seq [program, effectfulNew])) with
  | .value (.ref o) n =>
      match (n.heap.get o).ivars.lookup "@x", (n.heap.get o).ivars.lookup "@y", n.getLocal "a" with
        | some (.int 3), some (.int 3), .int 3 => true
        | _, _, _ => false
  | _ => false

#print axioms argument_effects_sem
#print axioms class_argument_effects_run
#print axioms allocating_args_sem
end Ratchet.Denote.Typed.PointClass
