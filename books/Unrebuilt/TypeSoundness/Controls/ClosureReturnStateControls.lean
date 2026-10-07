import Books.TypeSoundness.Rules.Closure.MainReturn
import Books.TypeSoundness.Rules.Closure.Current
import Books.TypeSoundness.Rules.Closure.Write
import Books.TypeSoundness.Conformance.Closure.Reify

/-! Full caller conformance survives a real captured write with a changed local type.
The main runtime permission returns only after the captured activation is popped. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.ClosureReturnStateControls
open RubyCore Checker Checker.Soundness

def frame (m : Machine) : RubyCore.Frame :=
  requiredClosureFrame m (reifiedClosure m [] [] .nil true) [] []
def written (m : Machine) : Machine := (pushMethodFrame m (frame m)).setLocal "x" .nil
private def bodyCtx : Ctx := ctx0.withoutRuntimeScope.withFrame none

theorem captured_nil_write_state {m : Machine} (hm : StateOk ctx0 [("x", .int)] .ivar0 m) :
    StateOk ctx0 [("x", .nilT)] .ivar0 (popMethodFrame (written m)) := by
  have hu : RootUncaptured m := by
    rw [RootUncaptured, ← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime rfl).captured
  have hslot : (m.frames.getD (m.stack.headD 0) default).locals.any (·.1 == "x") = true := by
    rw [← List.isSome_find?]
    cases hx : (m.frames.getD (m.stack.headD 0) default).locals.find? (·.1 == "x") with
    | some p => rfl
    | none =>
      have hv := (hm.env.1 "x" .int rfl).1
      rw [getLocal_uncaptured hu, hx] at hv
      simp [stripAlias, denM, isIntV] at hv
  have hb : StateOk bodyCtx [("x", .int)] .ivar0 (pushMethodFrame m (frame m)) := by
    apply requiredClosureFrame_state_of_env (ps := []) (args := [])
      (cl := reifiedClosure m [] [] .nil true) hm (ReframeFO.empty rfl rfl rfl rfl)
      rfl (ClosureScopeEq.current hm.frameInRange rfl)
    · exact currentClosureFrame_envOk (ps := []) (args := [])
        (cl := reifiedClosure m [] [] .nil true) hm (hm.runtime rfl).captured rfl trivial
        (by simp [reifiedClosure, blockLocals, isAliasTy]) (by
          intro p hp v hv
          simp only [List.nil_append, reifiedClosure, blockLocals, List.mem_singleton] at hp
          subst p; simpa only [denM] using hv)
    · intro _; rfl
  have hn : StateOk bodyCtx [("x", .nilT)] .ivar0 (written m) :=
    StateOk_setLocal (x := "x") (ρ := .nilT) hb
      (by simp [stripAlias, denM, isNilV]) rfl rfl rfl (by intro y σ h; cases h)
  have updated : StateOk ctx0 [("x", .nilT)] .ivar0 (m.setLocal "x" .nil) :=
    StateOk_setLocal (x := "x") (ρ := .nilT) hm
      (by simp [stripAlias, denM, isNilV]) rfl rfl rfl (by intro y σ h; cases h)
  have hfr := Framed_setLocal (pushMethodFrame m (frame m)) "x" .nil
  have hp := closure_pop_framed hm.frameInRange.2 hu (by rfl) hfr
  have henv : EnvOk [("x", .nilT)] (popMethodFrame (written m)) := by
    apply updated.env.reframe_uncaptured updated.frameInRange
      ⟨by rw [hp.stack]; exact hm.frameInRange.1,
        by rw [hp.stack]; exact Nat.lt_of_lt_of_le hm.frameInRange.2 hp.frames.size⟩
      ((Framed_setLocal m "x" .nil).frames.rootCaptured.trans hu)
      (captured_write_pop_frame hm.frameInRange rfl rfl "x" .nil hslot)
    intro p h v hv
    simp only [List.mem_singleton] at h
    subst p; simpa only [stripAlias, denM] using hv
  exact closure_pop_main_state hm (ReframeFO.empty rfl rfl rfl rfl) rfl rfl rfl rfl
    (fun _ => rfl) rfl hfr henv hn

theorem boot_captured_nil_write (hb : bootOkB = true) (value : Int) :
    StateOk ctx0 [("x", .nilT)] .ivar0
      (popMethodFrame (written (bootMachine.setLocal "x" (.int value)))) :=
  captured_nil_write_state (StateOk_setLocal (ρ := .int) (stateOk_boot hb)
    (by simp [stripAlias, denM, isIntV]) rfl rfl rfl (by intro y σ h; cases h))

theorem phase_flip_not_framed (m : Machine) :
    ¬ Framed m { m with preludeMode := !m.preludeMode } := by
  intro h
  have hp := h.phase
  cases he : m.preludeMode <;> simp_all

#print axioms captured_nil_write_state
#print axioms boot_captured_nil_write
#print axioms phase_flip_not_framed
end Checker.Soundness.Typed.ClosureReturnStateControls
