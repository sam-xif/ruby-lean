import Denote.Sem.MethodInstall
import Denote.Typed.MethodDispatch
import Denote.Typed.MethodStateControls

/-! A real-boot method write followed by dispatch, with full state conformance and
an annotation-checked body. Still not a checker admission or a corpus rung. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def identityDecl : Defn := ⟨"identity", [.req "x"], .var .lvar "x"⟩
private def reservedCtx : Ctx := { ctx0 with neg := { ctx0.neg with declared := ["identity"] } }
private def installedCtx : Ctx := { reservedCtx with pos := { reservedCtx.pos with defs := [identityDecl] } }
private def installed : Machine := installMethod bootMachine "identity" [.req "x"] (.var .lvar "x")

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

theorem identity_definition_step (hb : methodInstallBootOkB = true) :
    Interp.stepFn (evalFrom bootMachine (.def' "identity" [.req "x"] (.var .lvar "x"))) =
      .next (deliverA (.val (.sym "identity")) installed []) := by
  have hh : defHookQuietB bootMachine = true := by
    have h := hb
    simp only [methodInstallBootOkB, Bool.and_eq_true] at h
    exact h.2
  have hkont : bootMachine.kont = [] := by
    simp only [methodInstallBootOkB, methodBootOkB, Bool.and_eq_true, and_assoc] at hb
    exact List.isEmpty_iff.mp hb.2.2.2.1
  have hq : DefHookQuiet (evalFrom bootMachine
      (.def' "identity" [.req "x"] (.var .lvar "x"))) := defHookQuietB_sound hh
  have hs := step_def_install (name := "identity") (ps := [.req "x"])
    (body := .var .lvar "x") rfl (defHookQuiet_install (by decide) hq)
  simpa only [installed, installMethod, evalFrom, deliverA, Interp.withCtl, reCtl,
    definedMethod, hkont, Machine.currentFrame, Answer.ctl] using hs

theorem identity_installed_call (hb : methodInstallBootOkB = true) (v : Int) :
    ∃ next, Interp.finishSend installed installed.currentFrame.self .implicit "identity"
        [.int v] .none = .next next ∧ RunSpec installed next [] .int installedCtx := by
  simp only [methodInstallBootOkB, methodBootOkB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, beq_iff_eq, Bool.not_eq_true', and_assoc] at hb
  obtain ⟨hboot, hcap, hobj, hkont, howner, hclass, hselfB, hpayloadB, hchain, hpre, _hquiet⟩ := hb
  have hself : bootMachine.currentFrame.self = .ref Boot.mainId := by
    cases hs : bootMachine.currentFrame.self <;> simp_all
  have hpayload : (bootMachine.heap.get Boot.mainId).payload = .none := by
    cases hp : (bootMachine.heap.get Boot.mainId).payload <;> simp_all
  have hm₀ := stateOk_boot hboot
  have hm₁ : StateOk reservedCtx [] .ivar0 bootMachine := StateOk_reserveName hm₀ "identity"
  have hm : StateOk installedCtx [] .ivar0 installed := by
    have h := StateOk_defineTopMethod (d := identityDecl)
      (md := definedMethod bootMachine "identity" [.req "x"] (.var .lvar "x"))
      hm₁ (ReframeFO.empty rfl rfl rfl rfl) (by simp) rfl rfl rfl (by decide)
      hclass (by intro old ho; exact False.elim (List.not_mem_nil ho)) rfl rfl rfl
    have hnil : reservedCtx.defs = [] := rfl
    simpa only [installed, installMethod, howner, identityDecl, installedCtx, hnil] using h
  have hblk : bootMachine.currentFrame.blk = none := hm₀.blockTy
  have hcf : installed.currentFrame = bootMachine.currentFrame := rfl
  have hs : frameScope
      (requiredFrame installed.currentFrame.self "identity"
        (definedMethod bootMachine "identity" [.req "x"] (.var .lvar "x")) ["x"] [.int v]) =
      frameScope installed.currentFrame := by
    simp [frameScope, requiredFrame, definedMethod, hcf, hblk, hcap]
  obtain ⟨next, he, hr⟩ := required_method_runSpec (ps := [("x", .int)]) (e := .var .lvar "x")
    (Γb := [("x", .int)]) (fr := some ⟨"Object", "Object", "identity"⟩)
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
    (SemSafeCtxA.var rfl rfl)
  refine ⟨next, ?_, hr⟩
  have hrecv : installed.currentFrame.self = .ref Boot.mainId := (congrArg RubyCore.Frame.self hcf).trans hself
  rw [hrecv] at he ⊢
  rw [show Interp.finishSend installed (.ref Boot.mainId) .implicit "identity" [.int v] .none =
      Interp.enterUserMethod installed (.ref Boot.mainId) "identity"
        (definedMethod bootMachine "identity" [.req "x"] (.var .lvar "x")) [.int v] none from
    finishSend_installed hpayload (by rw [howner]; decide) (by rw [howner]; exact hclass)
      (by rw [howner]; exact hchain) hpre]
  exact he

#print axioms identity_installed_call
#print axioms identity_definition_step
end Ratchet.Denote.Typed
