import Denote.Controls.ClosureStoredReturnControls
import Denote.Rules.Closure.TrackedCall

/-! Copied closures retain their origins independently of the source binding. Neither
equal code nor an intact origin proves that native method lookup remains available. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ClosureTrackingControls
open RubyCore Ratchet Ratchet.Denote ClosureStoredControls ClosureStoredReturnControls

private def facts : LocalFacts := (LocalFacts.empty.write "f" true).copy "g" "f"
private def aliases (m : Machine) (code : ClosureCode) : Machine :=
  (stored m code "f").setLocal "g" ((stored m code "f").getLocal "f")
private def bindings (code : ClosureCode) : Env :=
  [("f", .clos code .ivar0 .never), ("g", .clos code .ivar0 .never)]

theorem alias_facts {m : Machine} (hm : StateOk ctx0 [] .ivar0 m)
    (hs : FrameSlots [] m) (code : ClosureCode) : LocalFactsOk facts (aliases m code) := by
  have hu : (m.frames.getD (m.stack.headD 0) default).captured = none := by
    rw [← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime rfl).captured
  have hf := (LocalFactsOk.empty hs).store hm hu "f" code
  have hstate := stored_state hm code "f"
  exact hf.copy hstate.frameInRange.2 (by
    change ((stored m code "f").frames.getD ((stored m code "f").stack.headD 0) default).captured = none
    rw [← currentFrame_headD hstate.frameInRange.1]
    exact (hstate.runtime rfl).captured) "g" "f"

theorem alias_state {m : Machine} (hm : StateOk ctx0 [] .ivar0 m)
    (code : ClosureCode) : StateOk ctx0 (bindings code) .ivar0 (aliases m code) := by
  have hs := stored_state hm code "f"
  exact StateOk_setLocal (x := "g") (ρ := .clos code .ivar0 .never) hs
    (hs.env.1 "f" _ rfl).1 rfl rfl rfl (by intro _ _ h; cases h)

/-- An abstract tracked caller, with two aliases, supplies every call premise. No
concrete payload identity or post-body caller environment is assumed. -/
theorem alias_integer_call {m : Machine} (hm : StateOk ctx0 [] .ivar0 m)
    (hs : FrameSlots [] m) (value : Int) :
    let code : ClosureCode := ⟨[], [], .int value, true, by simp [paramEqAll, exprEq]⟩
    RunSpec (aliases m code)
      (evalFrom (aliases m code) (.send (some (.var .lvar "g")) "call" [] none))
      (bindings code) .int ctx0 .ivar0 := by
  intro code
  have hf := alias_facts hm hs code
  have h := tracked_local_lambda_call (names := ["g", "f"])
    (alias_state hm code) hf (captureSlots_of_frameSlots (hf.slots _ rfl) _) "g" (by decide) rfl
    rfl
    rfl rfl rfl (ReframeFO.empty rfl rfl rfl rfl) rfl rfl (fun _ => rfl) rfl
    (by intro p hp; simp only [bindings, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> rfl)
    (by intro cl p hp v hv
        simp only [bindings, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;>
          exact ProcPres.empty_capture_den (m := aliases m code) (.refl _) hv)
    (κb := ctx0.withoutRuntimeScope.withFrame none) (Γb := bindings code) (Ib := .ivar0)
    SemSafeCtxA.intLit (ReframeFO.empty rfl rfl rfl rfl) rfl rfl (fun _ => rfl)
    (by intro n x σ hx _ v hv
        obtain ⟨y, hy⟩ := envGet?_mem hx
        simp only [bindings, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with hy | hy <;> cases hy <;>
          exact ProcPres.empty_capture_den (m := n) (.refl _) hv)
  simpa [bindings, captureEnv, deAlias, returnScopeCtx, Ctx.withoutRuntimeScope, Ctx.withFrame] using h

private def one : ClosureCode := ⟨[], [], .int 1, true, rfl⟩
private def sample : Machine := aliases bootMachine one
private def overwritten : Machine := sample.setLocal "f" .nil
private def afterWrite : LocalFacts := facts.write "f" false

#guard afterWrite.currentProcs == ["g"]
#guard currentProcB overwritten (overwritten.getLocal "g")
#guard !currentProcB overwritten (overwritten.getLocal "f")
#guard match Interp.run 30 (evalFrom overwritten
    (.send (some (.var .lvar "g")) "call" [] none)) with
  | .value (.int 1) _ => true
  | _ => false

-- Same heap, value and code, but the current frame is no longer the capture's owner.
private def otherFrame : Machine := pushMethodFrame sample default
#guard closB (.clos one .ivar0 .never) otherFrame (sample.getLocal "g")
#guard !currentProcB otherFrame (sample.getLocal "g")

-- Slot presence does not disappear when its value is nil.
#guard (LocalFacts.empty.write "hidden" false).slots == some ["hidden"]
#guard frameBinds (bootMachine.setLocal "hidden" .nil) (bootMachine.stack.headD 0) "hidden"

-- Native table readiness is independent of both capture identity and exact code.
#guard match Interp.run 50 (evalFrom sample
    (.class' "Proc" none (.def' "call" [] (.int 7)))) with
  | .value _ n => currentProcB n (n.getLocal "g") && !procCallReadyB n.heap &&
      !primitiveDispatchB n.heap (nameFreeN ctx0) &&
      primitiveDispatchB n.heap (fun name => name != "call" && nameFreeN ctx0 name)
  | _ => false

-- Interpreter-executed calls must not enter the pure builtin proof table.
#guard !(primitiveMethods.contains (Boot.procId, "call", "Proc#call"))

#print axioms alias_facts
#print axioms alias_state
#print axioms alias_integer_call
end Ratchet.Denote.Typed.ClosureTrackingControls
