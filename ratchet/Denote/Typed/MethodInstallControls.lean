import Denote.Sem.MethodInstall
import Denote.Typed.MethodDispatch
import Denote.Typed.MethodStateControls
import Denote.Typed.Primitive
import Denote.Typed.Bridge

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
private def addBodyChecked : Certified [("x", .int), ("y", .int)] addBody
    (installedCtx.withFrame (some ⟨"Object", "Object", "add"⟩)) :=
  (check 100 [("x", .int), ("y", .int)] addBody addBodyCert
    (installedCtx.withFrame (some ⟨"Object", "Object", "add"⟩))).get (by decide)

theorem add_body_from_certificate : SemSafeCtxA
    (installedCtx.withFrame (some ⟨"Object", "Object", "add"⟩)) [("x", .int), ("y", .int)] .ivar0
    addBody .int (installedCtx.withFrame (some ⟨"Object", "Object", "add"⟩))
    [("x", .int), ("y", .int)] .ivar0 := certified_context addBodyChecked

/-- Checks the concrete boot premises; not a per-program post-installation checker. -/
def methodInstallBootOkB : Bool := methodBootOkB &&
  (bootMachine.currentFrame.defmod == Boot.objectId) &&
  (bootMachine.heap.classPayload? Boot.objectId).isSome &&
  (match bootMachine.currentFrame.self with | .ref o => o == Boot.mainId | _ => false) &&
  (match (bootMachine.heap.get Boot.mainId).payload with | .none => true | _ => false) &&
  (ancestors bootMachine.heap (classOf bootMachine.heap (.ref Boot.mainId)) ==
    [Boot.objectId, Boot.kernelId, Boot.basicObjectId]) && !bootMachine.preludeMode &&
  defHookQuietB bootMachine

#guard methodInstallBootOkB

theorem add_definition_step (hb : methodInstallBootOkB = true) :
    Interp.stepFn (evalFrom bootMachine (.def' "add" [.req "x", .req "y"] addBody)) =
      .next (deliverA (.val (.sym "add")) installed []) := by
  have hh : defHookQuietB bootMachine = true := by
    have h := hb
    simp only [methodInstallBootOkB, Bool.and_eq_true] at h
    exact h.2
  have hkont : bootMachine.kont = [] := by
    simp only [methodInstallBootOkB, methodBootOkB, Bool.and_eq_true, and_assoc] at hb
    exact List.isEmpty_iff.mp hb.2.2.2.1
  have hq : DefHookQuiet (evalFrom bootMachine
      (.def' "add" [.req "x", .req "y"] addBody)) := defHookQuietB_sound hh
  have hs := step_def_install (name := "add") (ps := [.req "x", .req "y"])
    (body := toRuby addBody) rfl (defHookQuiet_install (by decide) hq)
  simpa only [installed, installMethod, evalFrom, deliverA, Interp.withCtl, reCtl,
    definedMethod, hkont, Machine.currentFrame, Answer.ctl] using hs

theorem add_installed_call (hb : methodInstallBootOkB = true) (x y : Int) :
    ∃ next, Interp.finishSend installed installed.currentFrame.self .implicit "add"
        [.int x, .int y] .none = .next next ∧ RunSpec installed next [] .int installedCtx := by
  simp only [methodInstallBootOkB, methodBootOkB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, beq_iff_eq, Bool.not_eq_true', and_assoc] at hb
  obtain ⟨hboot, hcap, hobj, hkont, howner, hclass, hselfB, hpayloadB, hchain, hpre, _hquiet⟩ := hb
  have hself : bootMachine.currentFrame.self = .ref Boot.mainId := by
    cases hs : bootMachine.currentFrame.self <;> simp_all
  have hpayload : (bootMachine.heap.get Boot.mainId).payload = .none := by
    cases hp : (bootMachine.heap.get Boot.mainId).payload <;> simp_all
  have hm₀ := stateOk_boot hboot
  have hm₁ : StateOk reservedCtx [] .ivar0 bootMachine := StateOk_reserveName hm₀ "add"
  have hm : StateOk installedCtx [] .ivar0 installed := by
    have h := StateOk_defineTopMethod (d := addDecl)
      (md := definedMethod bootMachine "add" [.req "x", .req "y"] (toRuby addBody))
      hm₁ (ReframeFO.empty rfl rfl rfl rfl) (by simp) rfl rfl rfl (by decide)
      hclass (by intro old ho; exact False.elim (List.not_mem_nil ho)) rfl rfl rfl
    have hnil : reservedCtx.defs = [] := rfl
    simpa only [installed, installMethod, howner, addDecl, installedCtx, hnil] using h
  have hblk : bootMachine.currentFrame.blk = none := hm₀.blockTy
  have hcf : installed.currentFrame = bootMachine.currentFrame := rfl
  have hs : frameScope
      (requiredFrame installed.currentFrame.self "add"
        (definedMethod bootMachine "add" [.req "x", .req "y"] (toRuby addBody)) ["x", "y"] [.int x, .int y]) =
      frameScope installed.currentFrame := by
    simp [frameScope, requiredFrame, definedMethod, hcf, hblk, hcap]
  obtain ⟨next, he, hr⟩ := required_method_runSpec (ps := [("x", .int), ("y", .int)]) (e := addBody)
    (Γb := [("x", .int), ("y", .int)]) (fr := some ⟨"Object", "Object", "add"⟩)
    hm (ReframeFO.empty rfl rfl rfl rfl) rfl hkont rfl rfl rfl rfl rfl
    (by simp [DenAll, denM, isIntV]) (by simp [FirstOrder, isAliasTy]) rfl
    (by simp) hs
    (fun x => by rw [constGet?_empty (κ := installedCtx.withFrame _) rfl,
      constGet?_empty (κ := installedCtx) rfl])
    (by
      simp only [FrameOk, currentFrame_pushMethodFrame]
      refine ⟨rfl, ?_⟩
      change isAName installed.heap installed.currentFrame.self "Object" = true
      rw [hcf]
      simpa only [installed, installMethod, isAName_defineMethod] using hobj)
    add_body_from_certificate
  refine ⟨next, ?_, hr⟩
  have hrecv : installed.currentFrame.self = .ref Boot.mainId := (congrArg RubyCore.Frame.self hcf).trans hself
  rw [hrecv] at he ⊢
  rw [show Interp.finishSend installed (.ref Boot.mainId) .implicit "add" [.int x, .int y] .none =
      Interp.enterUserMethod installed (.ref Boot.mainId) "add"
        (definedMethod bootMachine "add" [.req "x", .req "y"] (toRuby addBody)) [.int x, .int y] none from
    finishSend_installed hpayload (by rw [howner]; decide) (by rw [howner]; exact hclass)
      (by rw [howner]; exact hchain) hpre]
  exact he

#print axioms add_annotated_body
#print axioms add_body_from_certificate
#print axioms add_installed_call
#print axioms add_definition_step
end Ratchet.Denote.Typed
