import Denote.Typed.ClassStateControls
import Denote.Typed.MethodState
import Denote.Typed.InstanceInstall

/-! A class-valued self alone does not pin the definition scope or default visibility. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def unscopedClassCtx (cn : String) : Ctx :=
  let κ := classBodyCtx ctx0 cn
  { κ with scope := { κ.scope with runtimeClass := none } }
private def privateCopy (m : Machine) : Machine :=
  pushMethodFrame m { m.currentFrame with defVis := .priv }

-- This checked against the complete old StateOk, before adding a class-scope request.
theorem private_class_state {cn : String} {m : Machine}
    (hm : StateOk (unscopedClassCtx cn) [] .ivar0 m)
    (hcap : m.currentFrame.captured = none) (hloc : m.currentFrame.locals = []) :
    StateOk (unscopedClassCtx cn) [] .ivar0 (privateCopy m) := by
  have ht : ReframeFO (unscopedClassCtx cn) .ivar0 := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro τ h; change some (.clsOf cn) = some τ at h; cases h; rfl
    · intro τ h; cases h
    · intro x τ h; rw [constGet?_empty (by rfl)] at h; cases h
    · intro x τ h; change envGet? [] x = some τ at h; cases h
  have hcf : (privateCopy m).currentFrame = { m.currentFrame with defVis := .priv } :=
    currentFrame_pushMethodFrame ..
  have he : EnvOk [] (privateCopy m) := by
    refine ⟨?_, ?_⟩
    · intro x τ hx; cases hx
    · intro x _
      simp [privateCopy, pushMethodFrame, Machine.getLocal, Machine.getLocal.go,
        Array.getD_eq_getD_getElem?, hcap, hloc]
  exact StateOk_reframe hm ht rfl rfl
    (by rw [hcf]) (by rw [hcf]) (by rw [hcf]) (by rw [hcf]) (by rw [hcf]) rfl
    (fun h => False.elim (h rfl))
    (fun _ => rfl) (by simp [FrameInRange, privateCopy, pushMethodFrame]) he
    (by simpa only [FrameOk, classBodyCtx, hcf] using (show FrameOk none m from hm.frame))

theorem private_class_witness (hb : bootOkB = true) {cn : String}
    (hq : FreshClass.nativeFrameB ctx0 cn = true)
    (hn : constOwn bootMachine.heap Boot.objectId cn = none) (hne : cn.isEmpty = false) :
    ∃ m, StateOk (unscopedClassCtx cn) [] .ivar0 m ∧ m.currentFrame.defVis = .priv := by
  have hm := stateOk_boot hb
  obtain ⟨e, he, _⟩ := hm.core.classReady.objectEigen
  let m := RubyCore.Proof.Judgment.freshClsMachine bootMachine Boot.objectId
    bootMachine.currentFrame.cref cn cn e .nil
  have hentry : StateOk (unscopedClassCtx cn) [] .ivar0 m :=
    StateOk_forgetClassScope (FreshClass.state hm rfl rfl rfl (ClassTablesFrame.empty rfl rfl)
      (FreshClass.nativeFrameB_sound hq) hn hne he)
  refine ⟨privateCopy m, private_class_state hentry ?_ ?_, ?_⟩
  · rw [FreshClass.current_frame]; rfl
  · rw [FreshClass.current_frame]; rfl
  · simp only [privateCopy, currentFrame_pushMethodFrame]

-- An actual privacy change followed by def and an explicit call really raises.
#guard match Interp.enterClassBody bootMachine "Point" false none (.def' "answer" [] (.int 1)) with
  | .next m =>
      let m := m.setCurrentFrame { m.currentFrame with defVis := .priv }
      match Interp.run 100 m with
      | .value _ n => Semantics.typeStuck (Interp.run 100 (evalFrom n
          (.send (some (.send (some (.const "Point")) "new" [] none)) "answer" [] none)))
      | _ => false
  | _ => false

#print axioms private_class_state
#print axioms private_class_witness

theorem scoped_private_rejected {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {cn : String}
    (hr : κ.scope.runtimeClass = some cn) (hv : m.currentFrame.defVis = .priv) :
    ¬ StateOk κ Γ I m := by
  intro hm
  have h := hm.classRuntime.visibility (by rw [hr]; simp)
  simp only [defaultDefVis, hv] at h
  split at h <;> cases h

#guard !ctxEqB (classBodyCtx ctx0 "Point") (unscopedClassCtx "Point")
#guard !ctxEqB (classBodyCtx ctx0 "Point") (classBodyCtx ctx0 "Other")
#print axioms scoped_private_rejected
end Ratchet.Denote.Typed
