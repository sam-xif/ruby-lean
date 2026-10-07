import Books.TypeSoundness.Examples.YieldCall
import Books.TypeSoundness.Rules.Expr.Send
import Books.TypeSoundness.Conformance.Closure.Reify

/-! Real block allocation and ordinary method entry, followed by two checked yields and
addition. Controls include captured writes and a rejected claim that the method has no block. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.YieldMethodControls
open RubyCore Checker Checker.Soundness

private def arithmeticBody : Checker.Expr := .send (some (.var .lvar "x")) "*" [.int 10] none
private def writeBody : Checker.Expr := .vasgn .lvar "total"
  (.send (some (.var .lvar "total")) "+" [.var .lvar "x"] none)
private def allocated (m : Machine) (body : Checker.Expr) : Machine :=
  reifiedMachine m [.req "x"] [] (toRuby body) false
private def callStep (m : Machine) (body : Checker.Expr) : StepResult :=
  let entry := allocated m body
  Interp.enterUserMethod entry entry.currentFrame.self "twice" (YieldBody.method entry) []
    (some (.ref m.heap.objs.size))

theorem arithmetic {m : Machine} (hm : StateOk ctx0 [] .ivar0 m) (hk : m.kont = []) :
    StepSpec m [] .int (callStep m arithmeticBody) ctx0 .ivar0 := by
  let code : ClosureCode := ⟨[.req "x"], [], arithmeticBody, false, rfl⟩
  have h := YieldBody.call (o := m.heap.objs.size) (code := code) (name := "x") (body := arithmeticBody)
    (cl := reifiedClosure m [.req "x"] [] (toRuby arithmeticBody) false)
    (Γb := [("x", .int)]) (names := [])
    (reified_state hm [.req "x"] [] (toRuby arithmeticBody) false) hk rfl
    (by intro x τ hx; cases hx)
    (by simp only [reifiedMachine, pushHeap_get_self])
    ⟨rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl rfl rfl
    ((SemSafeCtxA.var rfl rfl).prim (.cons SemSafeCtxA.intLit .nil rfl)
      .intMul rfl (by intro h; cases h))
  exact h.rebase (.of_ext (reified_ext hm [.req "x"] [] (toRuby arithmeticBody) false))

theorem arithmetic_boot (hb : bootOkB = true) :
    StepSpec bootMachine [] .int (callStep bootMachine arithmeticBody) ctx0 .ivar0 :=
  arithmetic (stateOk_boot hb) bootMachine_kont

/-- Both callbacks can update total; its type survives while the first returned Integer
is held in the send continuation across the second callback. -/
theorem captured_write {m : Machine} (hm : StateOk ctx0 [("total", .int)] .ivar0 m)
    (hk : m.kont = []) (hd : CaptureSlots ["total"] [("total", .int)] m) :
    StepSpec m [("total", .int)] .int (callStep m writeBody) ctx0 .ivar0 := by
  let code : ClosureCode := ⟨[.req "x"], [], writeBody, false, rfl⟩
  have h := YieldBody.call (o := m.heap.objs.size) (code := code) (name := "x") (body := writeBody)
    (cl := reifiedClosure m [.req "x"] [] (toRuby writeBody) false)
    (Γb := [("x", .int), ("total", .int)]) (names := ["total"])
    (reified_state hm [.req "x"] [] (toRuby writeBody) false) hk rfl hd
    (by simp only [reifiedMachine, pushHeap_get_self])
    ⟨rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl rfl rfl
    (((SemSafeCtxA.var rfl rfl).prim (.cons (SemSafeCtxA.var rfl rfl) .nil rfl)
      .intAdd rfl (by intro h; cases h)).vasgn rfl rfl rfl)
  exact h.rebase (.of_ext (reified_ext hm [.req "x"] [] (toRuby writeBody) false))

theorem captured_write_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m writeBody) ctx0 .ivar0 := by
  have hm := stateOk_boot hb
  apply captured_write
    (StateOk_setLocal (ρ := .int) hm (by simp [stripAlias, denM, isIntV])
      rfl rfl rfl (by intro y σ h; cases h)) bootMachine_kont
  intro x τ hx
  by_cases he : x = "total"
  · subst x
    exact frameBinds_setLocal_self bootMachine "total" (.int initial) hm.frameInRange.2
      (by rw [rootFrame_eq_currentFrame hm.frameInRange.1]; exact (hm.runtime rfl).captured)
  · simp [envGet?, Ne.symm he] at hx

theorem absent_block_context_rejected {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {b : Value}
    (hb : m.currentFrame.blk = some b) : ¬ StateOk (κ.withBlockTy none) Γ I m := by
  intro h
  have hn := h.blockTy
  change m.currentFrame.blk = none at hn
  rw [hb] at hn
  cases hn

#print axioms arithmetic_boot
#print axioms captured_write
#print axioms captured_write_boot
#print axioms absent_block_context_rejected
end Checker.Soundness.Typed.YieldMethodControls
