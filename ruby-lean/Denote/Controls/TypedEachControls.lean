import Denote.Rules.Iterator.FlowEach
import Denote.Rules.Expr.Array

/-! A checked Integer body discharges the live loop contract. The return environment
must recover hidden caller types and reject a changed captured type. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.TypedEachControls
open RubyCore Ratchet Ratchet.Denote

private def body : Ratchet.Expr := .send (some (.var .lvar "x")) "+" [.int 1] none
private def closure (m : Machine) : Closure :=
  { params := [.req "x"], locals := [], body := toRuby body,
    captured := some ((popMethodFrame m).stack.headD 0),
    home := Interp.returnTarget (popMethodFrame m), lam := false }

private theorem body_typed (Γ : Env) : SemSafeCtxA (closureBodyCtx ctx0) (("x", .int) :: Γ)
    .ivar0 body .int (closureBodyCtx ctx0) (("x", .int) :: Γ) .ivar0 :=
  (SemSafeCtxA.var rfl rfl).prim (.cons SemSafeCtxA.intLit .nil rfl)
    .intAdd rfl (by intro h; cases h)

/-- No per-iteration body, return-state or invariant premise remains. -/
theorem integer_body {m : Machine} {o : ObjId}
    (hm : StateOk ctx0 [] .ivar0 (popMethodFrame m))
    (hv : denM (.arrayOf .int) (popMethodFrame m) (.ref o)) (brk : FrameId) (index : Nat) :
    StepSpec (popMethodFrame m) [] (.arrayOf .int)
      (eachArrayStep m (closure m) brk o index) ctx0 .ivar0 :=
  typed_each_step (cl := closure m) (name := "x") (body := body) (Γb := [("x", .int)])
    (names := []) hm rfl (by intro x τ hx; cases hx) hv
    rfl rfl rfl rfl rfl rfl rfl (body_typed []) brk index

/-- An Integer parameter must not replace the caller's hidden nil type. -/
theorem shadowed_caller {m : Machine} {o : ObjId}
    (hm : StateOk ctx0 [("x", .nilT)] .ivar0 (popMethodFrame m))
    (hv : denM (.arrayOf .int) (popMethodFrame m) (.ref o)) (brk : FrameId) (index : Nat) :
    StepSpec (popMethodFrame m) [("x", .nilT)] (.arrayOf .int)
      (eachArrayStep m (closure m) brk o index) ctx0 .ivar0 :=
  typed_each_step (cl := closure m) (name := "x") (body := body)
    (Γb := [("x", .int), ("x", .nilT)]) (names := []) hm rfl (by intro x τ hx; cases hx) hv
    rfl rfl rfl rfl rfl rfl rfl (body_typed [("x", .nilT)]) brk index

private def program : Ratchet.Expr :=
  .send (some (.array [.int 1, .int 2, .int 3])) "each" [] (some (.block [.req "x"] [] body))

/-- The exact 091 source, with actual receiver evaluation, block allocation and dispatch. -/
theorem source : SemSafeCtxA ctx0 [] .ivar0 program (.arrayOf .int) ctx0 [] .ivar0 := by
  apply SemFlow.erase
  exact SemFlow.each (names := [])
    (SemFlow.embed .unknown (SemSafeCtxA.arrayLit
      (.cons SemSafeCtxA.intLit (.cons SemSafeCtxA.intLit (.cons SemSafeCtxA.intLit .nil rfl) rfl) rfl) rfl))
    rfl rfl rfl rfl rfl rfl rfl (body_typed [])

theorem source_boot (hb : bootOkB = true) :
    RunSpec bootMachine (evalFrom bootMachine program) [] (.arrayOf .int) ctx0 .ivar0 :=
  source bootMachine (stateOk_boot hb)

#guard closureReturnEnv ["x"] ["y"] [("y", .int)] [("x", .int), ("y", .int)] == [("y", .int)]
#guard closureReturnEnv ["x"] ["y"] [("y", .int)] [("x", .int), ("y", .nilT)] != [("y", .int)]
#guard closureReturnEnv ["x"] [] [("x", .nilT)] [("x", .int)] != [("x", .int)]

#print axioms integer_body
#print axioms shadowed_caller
#print axioms source
#print axioms source_boot
end Ratchet.Denote.Typed.TypedEachControls
