import Checker.Controls.BoundBodyCheckControls
import Books.TypeSoundness.Rules.Method.FlowChecked
import Books.TypeSoundness.Controls.CallbackAliasControls

/-! Executable definition certificates feed actual &b entry and boot proofs.
No callback code or captured state was supplied to definition-side checking. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.BoundBodyControls
open RubyCore Checker Checker.Soundness BoundBodyCheckControls

private theorem body {e : Checker.Expr} (c : CheckedBoundCallbackBody ctx0 .ivar0 (decl e))
    (hl : c.localName = "b") (hp : c.blockArgs = [.int]) (hb : c.blockRet = .int)
    (hr : c.ret = .int) (hc : c.callback = false) :
    SemMethodFlow BoundCallbackControls.callback ⟨"Object", "Object", "run", false⟩
      [("b", .clos BoundCallbackControls.callback.code .ivar0 .never)] ⟨["b"]⟩ e .int false
      (c.out.instantiate BoundCallbackControls.callback.code) c.outFacts := by
  have h := checked_bound_callback_body_context c BoundCallbackControls.callback
    (by rw [hp]; rfl) (by rw [hb]; rfl)
  simpa only [hl, hr, hc, decl] using h

theorem direct_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (CallbackAliasControls.callStep m (call "b" 5)) ctx0 .ivar0 :=
  CallbackAliasControls.call_boot (body directChecked rfl rfl rfl rfl rfl) hb initial

theorem copied_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (CallbackAliasControls.callStep m copiedBody) ctx0 .ivar0 :=
  CallbackAliasControls.call_boot (body copiedChecked rfl rfl rfl rfl rfl) hb initial

theorem restored_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (CallbackAliasControls.callStep m restoredBody) ctx0 .ivar0 :=
  CallbackAliasControls.call_boot (body restoredChecked rfl rfl rfl rfl rfl) hb initial

theorem receiver_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (CallbackAliasControls.callStep m receiverBody) ctx0 .ivar0 :=
  CallbackAliasControls.call_boot (body receiverChecked rfl rfl rfl rfl rfl) hb initial

theorem saved_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (CallbackAliasControls.callStep m savedBody) ctx0 .ivar0 :=
  CallbackAliasControls.call_boot (body savedChecked rfl rfl rfl rfl rfl) hb initial

#print axioms direct_from_boot
#print axioms copied_from_boot
#print axioms restored_from_boot
#print axioms receiver_from_boot
#print axioms saved_from_boot
end Checker.Soundness.Typed.BoundBodyControls
