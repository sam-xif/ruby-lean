import Denote.Rules.Method.BoundEntry
import Denote.Rules.Method.BodyAssign
import Denote.Rules.Expr.Send
import Denote.Sem.Closure.Reify

/-! Explicit &b calls, including overwrite during argument evaluation and stable
captured writes. Sorbet 0.6.13405 accepts these typed Proc uses and rejects a call
after b has become nil (clink 240). Entry and dispatch use the actual interpreter. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.BoundCallbackControls
open RubyCore Ratchet Ratchet.Denote

private def writeBody : Ratchet.Expr := .vasgn .lvar "total"
  (.send (some (.var .lvar "total")) "+" [.var .lvar "x"] none)
def callback : CheckedCallback ctx0 [("total", .int)] .ivar0 where
  code := ⟨[.req "x"], [], writeBody, false, rfl⟩
  params := [("x", .int)]
  ret := .int
  names := ["total"]
  out := [("x", .int), ("total", .int)]
  required := rfl
  main := rfl
  returnFO := rfl
  inputTypes := rfl
  outputTypes := rfl
  fixed := rfl
  body := ((SemSafeCtxA.var rfl rfl).prim (.cons (SemSafeCtxA.var rfl rfl) .nil rfl)
    .intAdd rfl (by intro h; cases h)).vasgn rfl rfl rfl

private def boundEnv : Env := [("b", .clos callback.code .ivar0 .never)]
private def fr : Ratchet.Frame := ⟨"Object", "Object", "run", false⟩
private def overwriteArg : Ratchet.Expr := .seq [.vasgn .lvar "b" .nil, .int 5]
private def yieldArg : Ratchet.Expr := .yield' [.int 5]

private theorem overwrite_typed : SemMethod callback fr boundEnv overwriteArg .int [("b", .nilT)] :=
  ((SemMethod.ordinary SemSafeCtxA.nilLit).vasgn rfl rfl rfl rfl).seq
    (SemMethod.ordinary SemSafeCtxA.intLit)

private theorem yield_typed : SemMethod callback fr boundEnv yieldArg .int boundEnv :=
  SemMethod.yieldInt rfl rfl 5

private def allocated (m : Machine) : Machine := reifiedMachine m [.req "x"] [] (toRuby writeBody) false
private def method (m : Machine) (selector : String) (arg : Ratchet.Expr) : MethodDef :=
  { params := [.block (some "b")], body := toRuby (.send (some (.var .lvar "b")) selector [arg] none),
    owner := m.currentFrame.defmod, cref := m.currentFrame.cref }
private def callStep (m : Machine) (selector : String) (arg : Ratchet.Expr) : StepResult :=
  let entry := allocated m
  Interp.enterUserMethod entry entry.currentFrame.self "run" (method entry selector arg) []
    (some (.ref m.heap.objs.size))

theorem call {m : Machine} {arg : Ratchet.Expr} {Γm : Env} {selector : String}
    (he : SemMethod callback fr boundEnv arg .int Γm) (ht : activationReturnB Γm = true)
    (hplain : plainArgB arg = true) (hfree : nameFreeN ctx0 selector = true)
    (hselector : procCallNameB selector = true)
    (hm : StateOk ctx0 [("total", .int)] .ivar0 m) (hk : m.kont = [])
    (hd : CaptureSlots ["total"] [("total", .int)] m) :
    StepSpec m [("total", .int)] .int (callStep m selector arg) ctx0 .ivar0 := by
  have h := bound_callback_method_call he rfl ht hplain hfree hselector
    (md := method (allocated m) selector arg) (o := m.heap.objs.size)
    (cl := reifiedClosure m [.req "x"] [] (toRuby writeBody) false)
    (reified_state hm [.req "x"] [] (toRuby writeBody) false) hk rfl rfl rfl rfl rfl rfl rfl rfl
    hd (by simp only [reifiedMachine, pushHeap_get_self]) ⟨rfl, rfl, rfl, rfl⟩
    (by simp [classOf, reifiedMachine, pushHeap_get_self])
  exact h.rebase (.of_ext (reified_ext hm [.req "x"] [] (toRuby writeBody) false))

private theorem call_boot {arg : Ratchet.Expr} {Γm : Env} {selector : String}
    (he : SemMethod callback fr boundEnv arg .int Γm) (ht : activationReturnB Γm = true)
    (hplain : plainArgB arg = true) (hfree : nameFreeN ctx0 selector = true)
    (hselector : procCallNameB selector = true) (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m selector arg) ctx0 .ivar0 := by
  have hm := stateOk_boot hb
  apply call he ht hplain hfree hselector
    (StateOk_setLocal (ρ := .int) hm (by simp [stripAlias, denM, isIntV])
      rfl rfl rfl (by intro y σ h; cases h)) bootMachine_kont
  intro x τ hx
  by_cases hn : x = "total"
  · subst x
    exact frameBinds_setLocal_self bootMachine "total" (.int initial) hm.frameInRange.2
      (by rw [rootFrame_eq_currentFrame hm.frameInRange.1]; exact (hm.runtime rfl).captured)
  · simp [envGet?, Ne.symm hn] at hx

theorem direct_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m "call" (.int 5)) ctx0 .ivar0 :=
  call_boot (SemMethod.ordinary SemSafeCtxA.intLit) rfl rfl rfl rfl hb initial

theorem overwrite_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m "call" overwriteArg) ctx0 .ivar0 :=
  call_boot overwrite_typed rfl rfl rfl rfl hb initial

theorem bracket_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m "[]" overwriteArg) ctx0 .ivar0 :=
  call_boot overwrite_typed rfl rfl rfl rfl hb initial

/-- The saved block survives another invocation of itself while evaluating its argument. -/
theorem yield_argument_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m "call" yieldArg) ctx0 .ivar0 :=
  call_boot yield_typed rfl rfl rfl rfl hb initial

/-- Overwriting before receiver evaluation loses the required identity, even though
the implicit block remains in the frame and could still be invoked with yield. -/
theorem nil_binding_rejected {m : Machine} {o : ObjId} (x : String)
    (hi : m.stack.headD 0 < m.frames.size) (hb : m.currentFrame.blk = some (.ref o)) :
    ¬ MethodCallbackReceiver (m.setLocal x .nil) ((m.setLocal x .nil).getLocal x) := by
  intro h
  have hh := h.block
  rw [currentFrame_setLocal_blk, getLocal_setLocal_self _ _ _ hi, hb] at hh
  cases hh

#print axioms direct_from_boot
#print axioms overwrite_from_boot
#print axioms bracket_from_boot
#print axioms yield_argument_from_boot
#print axioms nil_binding_rejected
end Ratchet.Denote.Typed.BoundCallbackControls
