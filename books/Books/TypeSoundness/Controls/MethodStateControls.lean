import Books.TypeSoundness.Rules.Method.MethodState

/-! A real-boot, arbitrary-Integer post-dispatch call, from its annotated body proof.
This exercises full entry and return conformance, but does not claim checker admission
or method installation/lookup. The latter remain separate proof obligations. -/

set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

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
    (Γb := [("x", .int)]) (fr := some ⟨"Object", "Object", "identity", false⟩)
    hm (ReframeFO.empty rfl rfl rfl rfl) rfl bootMachine_kont rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [DenAll, denM, isIntV]) (by simp [FirstOrder, isAliasTy]) rfl
    (by simp) (by simp [frameScope, requiredFrame, identityMethod, hblk, ready.captured,
      ready.origin, ready.defFrame, hm.localAlias])
  · intro x
    rw [constGet?_empty (κ := ctx0.withFrame _) rfl,
      constGet?_empty (κ := ctx0) rfl]
  · simp only [FrameOk, Frame.recvTy, Bool.false_eq_true, ↓reduceIte, denM, currentFrame_pushMethodFrame]
    refine ⟨rfl, ?_, rfl⟩
    have hheap : ∀ (m : Machine) (f : RubyCore.Frame), (pushMethodFrame m f).heap = m.heap :=
      fun _ _ => rfl
    have hself : ∀ (s : Value) (md : MethodDef) (ps : List String) (as : List Value),
        (requiredFrame s "identity" md ps as).self = s := fun _ _ _ _ => rfl
    rw [hheap, hself, ready.self]
    exact ready.object
  · exact SemSafeCtxA.var rfl rfl

#print axioms identity_after_dispatch
end Checker.Soundness.Typed
