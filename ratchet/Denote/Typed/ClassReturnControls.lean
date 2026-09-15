import Denote.Typed.ClassRun
import Denote.Sanity

/-! Scope-only restoration retains executed declarations/reservations. The complete class
run control consumes a body certificate; class syntax itself remains outside validateD. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def point : Cls := ⟨"Point", none, [], [], false, [], [], []⟩
private def member : Defn := ⟨"x", [], .int 1⟩
private def afterBody : Ctx := instanceDeclCtx (classBodyCtx ctx0 "Point") point member

#guard ctxEqB (returnScopeCtx ctx0 afterBody) (instanceDeclCtx ctx0 point member)
#guard !ctxEqB (returnScopeCtx ctx0 afterBody) ctx0
#guard !(nameFreeN (returnScopeCtx ctx0 afterBody) "x")
#guard (returnScopeCtx ctx0 afterBody).scope.runtimeMain
#guard (returnScopeCtx ctx0 afterBody).scope.runtimeClass.isNone
#guard ((returnScopeCtx ctx0 afterBody).classes.map (·.name)) == ["Point"]

private def literalCert (κ : Ctx) (name : String) :
    Certified [] (.int 7) (classBodyCtx κ name) .ivar0 :=
  (check 5 [] (.int 7) (.intLit 7) (classBodyCtx κ name)).get (by rfl)

private theorem literal_body (κ : Ctx) (name : String) :
    SemSafeCtxA (classBodyCtx κ name) [] .ivar0 (.int 7) .int (classBodyCtx κ name) [] .ivar0 :=
  djudge_context (literalCert κ name).judged

theorem boot_class_literal_run (hb : bootOkB = true) {name : String}
    (hq : FreshClass.nativeFrameB ctx0 name = true)
    (hn : constOwn bootMachine.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    RunSpec bootMachine (evalFrom bootMachine (.class' name none (.int 7))) [] .int ctx0 .ivar0 :=
  class_runSpec (stateOk_boot hb) (ReframeFO.empty rfl rfl rfl rfl) rfl rfl rfl rfl rfl rfl
    (classBodyCtx_constGet rfl name) (by intro p hp; cases hp) rfl
    (ClassTablesFrame.empty rfl rfl) hq hn hne (literal_body ctx0 name)

-- Real definition inside a class, exit, explicit instance call, and retained caller local.
#guard match Interp.run 250 (evalFrom bootMachine (.seq [
    .vasgn .lvar "saved" (.int 7),
    .class' "Point" none (.seq [.vasgn .lvar "saved" (.int 9), .def' "answer" [] (.int 1)]),
    .send (some (.send (some (.const "Point")) "new" [] none)) "answer" [] none,
    .var .lvar "saved"])) with
  | .value (.int 7) _ => true
  | _ => false

#print axioms boot_class_literal_run
end Ratchet.Denote.Typed
