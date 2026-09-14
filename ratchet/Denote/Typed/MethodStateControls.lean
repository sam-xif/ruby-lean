import Denote.Typed.MethodState

/-! A real-boot, arbitrary-Integer post-dispatch call, from its annotated body proof.
This exercises full entry and return conformance, but does not claim checker admission
or method installation/lookup. The latter remain separate proof obligations. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def identityMethod : MethodDef :=
  { params := [.req "x"], body := toRuby (.var .lvar "x"),
    owner := bootMachine.currentFrame.defmod, cref := bootMachine.currentFrame.cref }

/-- Additional starting-frame facts the method boundary uses, checked on the real boot.
These must join the validator's boot contract when method admission is integrated. -/
def methodBootOkB : Bool := bootOkB && bootMachine.currentFrame.captured.isNone &&
  isAName bootMachine.heap bootMachine.currentFrame.self "Object" && bootMachine.kont.isEmpty

#guard methodBootOkB

theorem identity_after_dispatch (hb : methodBootOkB = true) (v : Int) :
    ∃ next, Interp.enterUserMethod bootMachine bootMachine.currentFrame.self "identity"
        identityMethod [.int v] none = .next next ∧ RunSpec bootMachine next [] .int := by
  simp only [methodBootOkB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at hb
  obtain ⟨⟨⟨hboot, hcap⟩, hobj⟩, hkont⟩ := hb
  have hm := stateOk_boot hboot
  have hblk : bootMachine.currentFrame.blk = none := hm.blockTy
  apply required_method_runSpec (ps := [("x", .int)]) (e := .var .lvar "x")
    (Γb := [("x", .int)]) (fr := some ⟨"Object", "Object", "identity"⟩)
    hm (ReframeFO.empty rfl rfl rfl rfl) rfl hkont rfl rfl rfl rfl rfl
    (by simp [DenAll, denM, isIntV]) (by simp [FirstOrder, isAliasTy]) rfl
    (by simp) (by simp [frameScope, requiredFrame, identityMethod, hblk, hcap])
  · intro x
    rw [constGet?_empty (κ := ctx0.withFrame _) rfl,
      constGet?_empty (κ := ctx0) rfl]
  · simp only [FrameOk, currentFrame_pushMethodFrame]
    refine ⟨rfl, ?_⟩
    change isAName bootMachine.heap bootMachine.currentFrame.self "Object" = true
    exact hobj
  · exact SemSafeCtxA.var rfl rfl

#print axioms identity_after_dispatch
end Ratchet.Denote.Typed
