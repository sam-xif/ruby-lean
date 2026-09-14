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

theorem identity_after_dispatch (hb : bootOkB = true) (v : Int) :
    ∃ next, Interp.enterUserMethod bootMachine bootMachine.currentFrame.self "identity"
        identityMethod [.int v] none = .next next ∧ RunSpec bootMachine next [] .int := by
  have hm := stateOk_boot hb
  have ready := hm.runtime rfl
  have hblk : bootMachine.currentFrame.blk = none := hm.blockTy
  apply required_method_runSpec (ps := [("x", .int)]) (e := .var .lvar "x")
    (Γb := [("x", .int)]) (fr := some ⟨"Object", "Object", "identity"⟩)
    hm (ReframeFO.empty rfl rfl rfl rfl) rfl bootMachine_kont rfl rfl rfl rfl rfl
    (by simp [DenAll, denM, isIntV]) (by simp [FirstOrder, isAliasTy]) rfl
    (by simp) (by simp [frameScope, requiredFrame, identityMethod, hblk, ready.captured])
  · intro x
    rw [constGet?_empty (κ := ctx0.withFrame _) rfl,
      constGet?_empty (κ := ctx0) rfl]
  · simp only [FrameOk, currentFrame_pushMethodFrame]
    refine ⟨rfl, ?_⟩
    change isAName bootMachine.heap bootMachine.currentFrame.self "Object" = true
    rw [ready.self]
    exact ready.object
  · exact SemSafeCtxA.var rfl rfl

#print axioms identity_after_dispatch
end Ratchet.Denote.Typed
