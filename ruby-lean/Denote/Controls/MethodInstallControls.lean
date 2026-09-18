import Denote.Sem.Instance.MethodInstall
import Denote.Rules.Method.MethodDispatch
import Denote.Controls.MethodStateControls
import Denote.Rules.Primitive.Primitive
import Denote.Rules.Method.MethodLookup

/-! A real-boot method write followed by dispatch, with full state conformance and
an annotation-checked body. Still not a checker admission or a corpus rung. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def addBody : Ratchet.Expr :=
  .send (some (.var .lvar "x")) "+" [.var .lvar "y"] none
private def addDecl : Defn := ⟨"add", [.req "x", .req "y"], addBody⟩
private def reservedCtx : Ctx := { ctx0 with neg := { ctx0.neg with declared := ["add"] } }
private def installedCtx : Ctx := { reservedCtx with pos := { reservedCtx.pos with defs := [addDecl] } }
private def installed : Machine := installMethod bootMachine "add" [.req "x", .req "y"] (toRuby addBody)

/-- The body is proved from its annotations, independently of any caller or argument values. -/
theorem add_annotated_body {κ : Ctx} {I : Ty} (hf : nameFreeN κ "+" = true) :
    SemSafeCtxA κ [("x", .int), ("y", .int)] I addBody .int
      κ [("x", .int), ("y", .int)] I :=
  (SemSafeCtxA.var rfl rfl).prim (.cons (SemSafeCtxA.var rfl rfl) .nil rfl)
    .intAdd hf (by intro h; cases h)

private def addBodyCert : Deriv :=
  .prim (.var .lvar "x") "+" [.var .lvar "y"] .int .int

/-- The certificate is checked under the annotations in the installed method context.
No argument values or concrete execution enter this check. -/
private def addBodyChecked : CheckedBody
    (installedCtx.withFrame (some ⟨"Object", "Object", "add"⟩)) .ivar0 addDecl :=
  (checkMethodBody 100 (installedCtx.withFrame (some ⟨"Object", "Object", "add"⟩)) .ivar0 addDecl
    (.defDecl "add" [("x", .int), ("y", .int)] .int addBodyCert)).get (by decide)

theorem add_body_from_certificate : SemSafeCtxA
    (installedCtx.withFrame (some ⟨"Object", "Object", "add"⟩)) [("x", .int), ("y", .int)] .ivar0
    addBody .int (installedCtx.withFrame (some ⟨"Object", "Object", "add"⟩))
    [("x", .int), ("y", .int)] .ivar0 := checked_body_context addBodyChecked

theorem add_definition_step (hb : bootOkB = true) :
    Interp.stepFn (evalFrom bootMachine (.def' "add" [.req "x", .req "y"] addBody)) =
      .next (deliverA (.val (.sym "add")) installed []) := by
  have ready := (stateOk_boot hb).runtime rfl
  have hq : DefHookQuiet (evalFrom bootMachine
      (.def' "add" [.req "x", .req "y"] addBody)) := mainReady_defHookQuiet (m := bootMachine) ready
  have hs := step_def_install (name := "add") (ps := [.req "x", .req "y"])
    (body := toRuby addBody) rfl (defHookQuiet_install (by decide) hq)
  simpa only [installed, installMethod, evalFrom, deliverA, Interp.withCtl, reCtl,
    definedMethod, bootMachine_kont, Machine.currentFrame, Answer.ctl] using hs

theorem add_installed_call (hb : bootOkB = true) (x y : Int) :
    ∃ next, Interp.finishSend installed installed.currentFrame.self .implicit "add"
        [.int x, .int y] .none = .next next ∧ RunSpec installed next [] .int installedCtx := by
  have hm₀ := stateOk_boot hb
  have ready := hm₀.runtime rfl
  have hm₁ : StateOk reservedCtx [] .ivar0 bootMachine := StateOk_reserveName hm₀ "add"
  have hm : StateOk installedCtx [] .ivar0 installed := by
    have h := StateOk_defineTopMethod (d := addDecl)
      (md := definedMethod bootMachine "add" [.req "x", .req "y"] (toRuby addBody))
      hm₁ (ReframeFO.empty rfl rfl rfl rfl) (by simp) rfl rfl rfl (by decide) (by decide)
      ready.classLive (by intro old ho; exact False.elim (List.not_mem_nil ho)) rfl rfl rfl
      (definedMethod_code ready.owner ready.cref ready.phase)
    have hnil : reservedCtx.defs = [] := rfl
    simpa only [installed, installMethod, ready.owner, addDecl, installedCtx, hnil] using h
  exact checked_top_call (decl := addDecl) (args := [.int x, .int y])
    addBodyChecked hm (by change addDecl ∈ [addDecl]; simp)
    (ReframeFO.empty rfl rfl rfl rfl) rfl rfl (by simp) bootMachine_kont (by rfl)
    (by change DenAll [.int, .int] installed [.int x, .int y]; simp [DenAll, denM, isIntV])
    rfl rfl

#print axioms add_annotated_body
#print axioms add_body_from_certificate
#print axioms add_installed_call
#print axioms add_definition_step
end Ratchet.Denote.Typed
