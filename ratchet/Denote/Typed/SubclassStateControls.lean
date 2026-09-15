import Denote.Typed.SubclassStateEntry
import Denote.Typed.ClassHeaderRun
import Denote.Typed.Bridge
import Denote.Sanity

/-! Full-state control after a real checked parent-class run, followed by actual subclass
entry. The unexecuted child body is arbitrary; this is not a body-acceptance theorem. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SubclassStateControls
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshClsMachine)

private def parentBodyCtx : Ctx := classHeaderCtx (classBodyCtx ctx0 "Carrier") "Carrier"
private def parentCtx : Ctx := returnScopeCtx ctx0 parentBodyCtx
private def parentProgram : Ratchet.Expr := .class' "Carrier" none (.int 7)
private def parentEigen : ObjId := (bootMachine.heap.get Boot.objectId).eigen.getD 0
private def parentEntry : Machine := freshClsMachine (evalFrom bootMachine parentProgram)
  Boot.objectId bootMachine.currentFrame.cref "Carrier" "Carrier" parentEigen (.int 7)
private def parentMachine : Machine := deliver (popMethodFrame parentEntry) (.int 7) []

private def bodyCert : Certified [] (.int 7) parentBodyCtx .ivar0 :=
  (check 5 [] (.int 7) (.intLit 7) parentBodyCtx).get (by rfl)

private theorem parent_run (hb : bootOkB = true) :
    RunSpec bootMachine (evalFrom bootMachine parentProgram) [] .int parentCtx .ivar0 := by
  exact class_header_runSpec (stateOk_boot hb) (ReframeFO.empty rfl rfl rfl rfl)
    rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl) (by intro p hp; cases hp) rfl
    (ClassTablesFrame.empty rfl rfl) (by decide) (by decide) (by decide)
    rfl (by constructor <;> decide) (by decide) (by decide) (djudge_context bodyCert.judged)

private theorem parent_execution (hb : bootOkB = true) :
    runA 3 (evalFrom bootMachine parentProgram) = .ans (.val (.int 7)) parentMachine 0 := by
  have hm := stateOk_boot hb
  obtain ⟨ep, he, hs⟩ := stepFn_class_fresh (name := "Carrier") (body := .int 7) hm rfl
    (hm.freshClassName (by decide)) (by decide)
  have heq : parentEigen = ep := by simp only [parentEigen, he, Option.getD_some]
  rw [← heq] at hs
  change Interp.stepFn (evalFrom bootMachine parentProgram) = .next parentEntry at hs
  rw [runA_succ (answerPoint_evalFrom _ _), hs]
  rfl

private theorem parent_state (hb : bootOkB = true) : StateOk parentCtx [] .ivar0 parentMachine :=
  ((parent_run hb).2 3 (.val (.int 7)) parentMachine 0 (parent_execution hb)).2.2 _ rfl

private theorem tables : ClassTablesFrame parentCtx "Relay" parentMachine := by
  refine ⟨?_, ?_, ?_⟩
  · intro cn τ ht; simp [constGet?, constPaths, parentCtx, parentBodyCtx, returnScopeCtx,
      classHeaderCtx, classBodyCtx, ctx0, Ctx.consts, Ctx.frame, envGet?] at ht
  · intro owner cn τ ht; cases ht
  · intro owner cn c ht
    have hne := unqualifiedClassB_ne_path (by decide : unqualifiedClassB "Carrier" = true) owner cn
    change clsGet? [classHeader "Carrier"] (owner ++ "::" ++ cn) = some c at ht
    simp [clsGet?, classHeader, hne] at ht

/-- This witness starts from the real boot, checks and runs the parent body, restores
main conformance, and then supplies all entry obligations for an unrelated class name. -/
theorem boot_parent_child_state (hb : bootOkB = true) (body : RubyCore.Expr) :
    ∃ n, Interp.enterClassBody parentMachine "Relay" false
        (some bootMachine.heap.objs.size) body = .next n ∧
      StateOk (classBodyCtx parentCtx "Relay") [] .ivar0 n := by
  exact Subclass.enter_declared_state (c := classHeader "Carrier") (parent_state hb)
    rfl rfl rfl tables (by decide) (by simp [parentCtx, parentBodyCtx, returnScopeCtx,
      classHeaderCtx, classBodyCtx, ctx0, Ctx.classes])
    (classNamed_freshClass ((stateOk_boot hb).runtime rfl).classLive
      (stateOk_boot hb).core.classReady.chains.boot.2.2.2.2) (by decide)
    ((parent_state hb).freshClassName (by decide)) (by decide)

-- The complete incoming state actually retains a published allocator and the executed
-- global-name bound; neither is an empty-table premise in the full-state entry theorem.
example (hb : bootOkB = true) : AllocatorsOk ["Carrier"] parentMachine.heap :=
  (parent_state hb).allocators

theorem boot_parent_child_step (hb : bootOkB = true) (body : RubyCore.Expr) :
    ∃ n, Interp.stepFn (reCtl parentMachine (.value (.ref bootMachine.heap.objs.size))
        [.classDefK "Relay" body]) = .next n ∧
      StateOk (classBodyCtx parentCtx "Relay") [] .ivar0 n := by
  exact Subclass.step_declared_state (c := classHeader "Carrier")
    (StateOk_reCtl (parent_state hb) _ _) rfl rfl rfl rfl rfl (tables.heap rfl)
    (by decide) (by simp [parentCtx, parentBodyCtx, returnScopeCtx,
      classHeaderCtx, classBodyCtx, ctx0, Ctx.classes])
    (classNamed_freshClass ((stateOk_boot hb).runtime rfl).classLive
      (stateOk_boot hb).core.classReady.chains.boot.2.2.2.2)
    (by decide) (by decide) (by decide)

#guard subclassBaseFrameB parentCtx "Carrier"
#guard freshClassNameB parentCtx "Relay"
#guard !freshClassNameB parentCtx "Carrier"

#print axioms parent_run
#print axioms parent_execution
#print axioms parent_state
#print axioms boot_parent_child_state
#print axioms boot_parent_child_step
end Ratchet.Denote.Typed.SubclassStateControls
