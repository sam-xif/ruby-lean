import Denote.Controls.ClosureStoredControls
import Denote.Rules.Closure.ProjectedReturn

/-! Full stored-lambda caller restoration retains f's exact code type. Assignment proves
f's physical binding; unrelated hidden nil slots need not be enumerated. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ClosureStoredReturnControls
open RubyCore Ratchet Ratchet.Denote ClosureStoredControls

private def bodyCtx : Ctx := ctx0.withoutRuntimeScope.withFrame none
def frame (m : Machine) (code : ClosureCode) (name : String) : RubyCore.Frame :=
  requiredClosureFrame (stored m code name) (payload m code) [] []

theorem stored_slots {m : Machine} (hm : StateOk ctx0 [] .ivar0 m) (hd : FrameSlots [] m)
    (code : ClosureCode) (name : String) : FrameSlots [name] (stored m code name) := by
  have hu : (m.frames.getD (m.stack.headD 0) default).captured = none := by
    rw [← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime rfl).captured
  exact FrameSlots.setLocal (m := reifiedMachine m (toRubyParams code.params) code.locals
    (toRuby code.body) code.lam) hd hm.frameInRange.2 hu name (.ref m.heap.objs.size)

theorem stored_main_return {m n : Machine} (hm : StateOk ctx0 [] .ivar0 m)
    (code : ClosureCode) (name : String) (hls : code.locals = [])
    (h : Framed (pushMethodFrame (stored m code name) (frame m code name)) n)
    (hn : StateOk bodyCtx [(name, .clos code .ivar0 .never)] .ivar0 n) :
    StateOk ctx0 [(name, .clos code .ivar0 .never)] .ivar0 (popMethodFrame n) := by
  have he := closure_projected_main_state (stored_state hm code name)
    (ReframeFO.empty rfl rfl rfl rfl) rfl rfl rfl rfl (fun _ => rfl) (f := frame m code name)
    (by rfl) (names := [name]) (by
      intro x τ hx
      have hxname : x = name := by
        by_cases he : x = name
        · exact he
        · simp [envGet?, Ne.symm he] at hx
      subst x
      have hb : frameBinds (stored m code name) ((stored m code name).stack.headD 0) name = true := by
        rw [stored, setLocal_eq_setAt]
        have hu : (m.frames.getD (m.stack.headD 0) default).captured = none := by
          rw [← currentFrame_headD hm.frameInRange.1]
          exact (hm.runtime rfl).captured
        have ho := setLocal_owner_uncaptured (m := reifiedMachine m (toRubyParams code.params)
          code.locals (toRuby code.body) code.lam) hu name (m.frames.size + 1)
        change frameBinds (setAt _ name _ _) (m.stack.headD 0) name = true
        simp only [reifiedMachine] at ho ⊢
        rw [ho]
        have he := setAt_find_self (reifiedMachine m (toRubyParams code.params)
          code.locals (toRuby code.body) code.lam) name (.ref m.heap.objs.size)
          (m.stack.headD 0) hm.frameInRange.2
        simp only [reifiedMachine] at he
        simp only [frameBinds, ← List.isSome_find?, he, Option.isSome_some]
      simpa using hb)
    (by intros; simp [frame, requiredClosureFrame, payload, reifiedClosure, hls]) h hn (by
      intro x τ hx _ v hv
      obtain ⟨z, hz⟩ := envGet?_mem hx
      simp only [List.mem_singleton] at hz
      cases hz
      exact ProcPres.empty_capture_den (m := n) (n := popMethodFrame n) (.refl _) hv)
  change StateOk ctx0 (captureEnv [name] [(name, .clos code .ivar0 .never)]) .ivar0
    (popMethodFrame n) at he
  simpa [captureEnv, deAlias] using he

theorem boot_slots (hb : bootOkB = true) : FrameSlots [] bootMachine := by
  have hl : localsEmptyB bootMachine = true := by
    simp only [bootOkB, bootStateB, bootStateBaseB, Bool.and_eq_true] at hb
    simp_all only
  simp only [localsEmptyB, Bool.and_eq_true, List.isEmpty_iff] at hl
  have hempty : (bootMachine.frames[bootMachine.stack.head?.getD 0]?.getD default).locals = [] :=
    hl.1
  have hs (s : List FrameId) : s.headD 0 = s.head?.getD 0 := by cases s <;> rfl
  intro x
  simp only [frameBinds, Array.getD_eq_getD_getElem?, hs, hempty, List.any_nil,
    List.contains_nil]

theorem boot_stored_main_return {n : Machine} (hb : bootOkB = true)
    (code : ClosureCode) (hls : code.locals = [])
    (h : Framed (pushMethodFrame (stored bootMachine code "f") (frame bootMachine code "f")) n)
    (hn : StateOk bodyCtx [("f", .clos code .ivar0 .never)] .ivar0 n) :
    StateOk ctx0 [("f", .clos code .ivar0 .never)] .ivar0 (popMethodFrame n) :=
  stored_main_return (stateOk_boot hb) code "f" hls h hn

#print axioms stored_slots
#print axioms stored_main_return
#print axioms boot_slots
#print axioms boot_stored_main_return
end Ratchet.Denote.Typed.ClosureStoredReturnControls
