import Denote.Rules.Method.BodyAssign
import Denote.Rules.Method.BodyEntry
import Denote.Rules.Method.BodyPrimitive
import Denote.Rules.Expr.Send
import Denote.Rules.Expr.Array
import Denote.Sem.Closure.Reify
import Denote.Examples.YieldBody

/-! General source rules type assignments around repeated yields. The method and block
both write total, but the block captures the outer caller and skips the method's local. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.MethodTypingControls
open RubyCore Ratchet Ratchet.Denote

private def writeBody : Ratchet.Expr := .vasgn .lvar "total"
  (.send (some (.var .lvar "total")) "+" [.var .lvar "x"] none)
private def code : ClosureCode := ⟨[.req "x"], [], writeBody, false, rfl⟩
private def callback : CheckedCallback ctx0 [("total", .int)] .ivar0 where
  code := code
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

private def mixedBody : Ratchet.Expr := .seq [.vasgn .lvar "total" .nil,
  .vasgn .lvar "total" (.yield' [.int 1]), .vasgn .lvar "result" (.yield' [.int 2]),
  .send (some (.var .lvar "total")) "+" [.var .lvar "result"] none]
private def nestedBody : Ratchet.Expr := .yield' [.vasgn .lvar "total" (.yield' [.int 1])]
private def formattedBody : Ratchet.Expr :=
  .send (some (.send (some (.yield' [.int 1])) "to_s" [] none)) "length" [] none
private def arrayBody : Ratchet.Expr := .send (some (.array [.int 10, .int 20])) "[]" [.yield' [.int 1]] none
private def divideBody : Ratchet.Expr := .send (some (.yield' [.int 0])) "/" [.yield' [.int 0]] none

/-- No special twice/mixed rule: ordinary expressions, assignment, yield and sequence
construct this body proof. Each later callback receives the restored activation invariant. -/
theorem judged (fr : Ratchet.Frame) :
    SemMethod callback fr [] mixedBody .int [("total", .int), ("result", .int)] := by
  have h0 : SemMethod callback fr [] (.vasgn .lvar "total" .nil) .nilT [("total", .nilT)] :=
    (SemMethod.ordinary SemSafeCtxA.nilLit).vasgn rfl rfl rfl rfl
  have h1 : SemMethod callback fr [("total", .nilT)] (.vasgn .lvar "total" (.yield' [.int 1]))
      .int [("total", .int)] := (SemMethod.yieldInt rfl rfl 1).vasgn rfl rfl rfl rfl
  have h2 : SemMethod callback fr [("total", .int)] (.vasgn .lvar "result" (.yield' [.int 2]))
      .int [("total", .int), ("result", .int)] := (SemMethod.yieldInt rfl rfl 2).vasgn rfl rfl rfl rfl
  exact SemMethod.sequence (.cons h0 (.cons h1 (.cons h2 (.last (SemMethod.ordinary
    ((SemSafeCtxA.var rfl rfl).prim (.cons (SemSafeCtxA.var rfl rfl) .nil rfl)
      .intAdd rfl (by intro h; cases h)))))))

theorem nested_judged (fr : Ratchet.Frame) :
    SemMethod callback fr [] nestedBody .int [("total", .int)] :=
  ((SemMethod.yieldInt rfl rfl 1).vasgn rfl rfl rfl rfl).yieldOne rfl rfl trivial

/-- Rung 094's actual body now follows from general source rules. -/
theorem twice_judged (fr : Ratchet.Frame) : SemMethod callback fr [] YieldBody.twice .int [] :=
  (SemMethod.yieldInt rfl rfl 1).prim (.cons (SemMethod.yieldInt rfl rfl 2) .nil rfl)
    .intAdd rfl (by intro h; cases h)

theorem formatted_judged (fr : Ratchet.Frame) : SemMethod callback fr [] formattedBody .int [] :=
  ((SemMethod.yieldInt rfl rfl 1).prim .nil .intToS rfl (by intro h; cases h)).prim
    .nil .strLength rfl (by intro; rfl)

/-- The allocated array is saved while the index expression invokes a captured write. -/
theorem array_judged (fr : Ratchet.Frame) : SemMethod callback fr [] arrayBody (.nilable .int) [] :=
  (SemMethod.ordinary (SemSafeCtxA.arrayLit
    (.cons SemSafeCtxA.intLit (.cons SemSafeCtxA.intLit .nil rfl) rfl) rfl)).prim
    (.cons (SemMethod.yieldInt rfl rfl 1) .nil rfl) (.arrayIndex rfl) rfl (by intro h; cases h)

theorem divide_judged (fr : Ratchet.Frame) : SemMethod callback fr [] divideBody .int [] :=
  (SemMethod.yieldInt rfl rfl 0).prim (.cons (SemMethod.yieldInt rfl rfl 0) .nil rfl)
    .intDiv rfl (by intro h; cases h)

private def allocated (m : Machine) : Machine := reifiedMachine m [.req "x"] [] (toRuby writeBody) false
private def method (m : Machine) (body : Ratchet.Expr) : MethodDef :=
  { params := [], body := toRuby body, owner := m.currentFrame.defmod, cref := m.currentFrame.cref }
private def callStep (m : Machine) (body : Ratchet.Expr) : StepResult :=
  let entry := allocated m
  Interp.enterUserMethod entry entry.currentFrame.self "mixed" (method entry body) []
    (some (.ref m.heap.objs.size))

theorem call {m : Machine} {body : Ratchet.Expr} {Γm : Env} {τ : Ty}
    (hbody : SemMethod callback ⟨"Object", "Object", "mixed", false⟩ [] body τ Γm) (hτ : FirstOrder τ = true)
    (hm : StateOk ctx0 [("total", .int)] .ivar0 m)
    (hk : m.kont = []) (hd : CaptureSlots ["total"] [("total", .int)] m) :
    StepSpec m [("total", .int)] τ (callStep m body) ctx0 .ivar0 := by
  have h := SemMethod.call0 (cb := callback) (md := method (allocated m) body) (o := m.heap.objs.size)
    (cl := reifiedClosure m [.req "x"] [] (toRuby writeBody) false)
    hbody
    (reified_state hm [.req "x"] [] (toRuby writeBody) false) hk hτ rfl rfl rfl rfl rfl rfl rfl rfl
    hd (by simp only [reifiedMachine, pushHeap_get_self]) ⟨rfl, rfl, rfl, rfl⟩
  exact h.rebase (.of_ext (reified_ext hm [.req "x"] [] (toRuby writeBody) false))

private theorem call_boot {body : Ratchet.Expr} {Γm : Env} {τ : Ty}
    (hbody : SemMethod callback ⟨"Object", "Object", "mixed", false⟩ [] body τ Γm) (hτ : FirstOrder τ = true)
    (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] τ (callStep m body) ctx0 .ivar0 := by
  have hm := stateOk_boot hb
  apply call hbody hτ
    (StateOk_setLocal (ρ := .int) hm (by simp [stripAlias, denM, isIntV])
      rfl rfl rfl (by intro y σ h; cases h)) bootMachine_kont
  intro x τ hx
  by_cases he : x = "total"
  · subst x
    exact frameBinds_setLocal_self bootMachine "total" (.int initial) hm.frameInRange.2
      (by rw [rootFrame_eq_currentFrame hm.frameInRange.1]; exact (hm.runtime rfl).captured)
  · simp [envGet?, Ne.symm he] at hx

/-- Real allocation, method entry and return from boot, for every initial captured Integer. -/
theorem from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m mixedBody) ctx0 .ivar0 :=
  call_boot (judged _) rfl hb initial

theorem nested_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m nestedBody) ctx0 .ivar0 :=
  call_boot (nested_judged _) rfl hb initial

theorem twice_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m YieldBody.twice) ctx0 .ivar0 :=
  call_boot (twice_judged _) rfl hb initial

theorem formatted_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m formattedBody) ctx0 .ivar0 :=
  call_boot (formatted_judged _) rfl hb initial

theorem array_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] (.nilable .int) (callStep m arrayBody) ctx0 .ivar0 :=
  call_boot (array_judged _) rfl hb initial

/-- At initial=0 this raises ZeroDivisionError; that remains a typed escape. -/
theorem divide_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m divideBody) ctx0 .ivar0 :=
  call_boot (divide_judged _) rfl hb initial

#print axioms judged
#print axioms from_boot
#print axioms nested_from_boot
#print axioms twice_from_boot
#print axioms formatted_from_boot
#print axioms array_from_boot
#print axioms divide_from_boot
end Ratchet.Denote.Typed.MethodTypingControls
