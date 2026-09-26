import Denote.Rules.Method.BodyAssign
import Denote.Rules.Method.BodyEntry
import Denote.Rules.Method.BodyPrimitive
import Denote.Rules.Expr.Send
import Denote.Rules.Expr.Array
import Denote.Sem.Closure.Reify
import Denote.Examples.YieldBody
import Denote.Rules.Method.BodyBridge
import Denote.Rules.Method.BodyChecked
import Ratchet.Controls.CallbackBodyCheckControls

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

private theorem yield_int {Γ : Env} {fr : Ratchet.Frame} (n : Int) (ht : activationReturnB Γ = true) :
    DMethod ctx0 .ivar0 fr [.int] .int Γ (.yield' [.int n]) .int Γ :=
  .yieldOne (.ordinary fun _ => .intLit) ht rfl

/-- The definition-side derivations mention no callback code, parameter names or captures.
Every ordinary premise is checked for all codes before any actual callback is supplied. -/
theorem mixed_syntax (fr : Ratchet.Frame) :
    DMethod ctx0 .ivar0 fr [.int] .int [] mixedBody .int [("total", .int), ("result", .int)] := by
  have h0 : DMethod ctx0 .ivar0 fr [.int] .int [] (.vasgn .lvar "total" .nil) .nilT [("total", .nilT)] :=
    .vasgn (.ordinary fun _ => .nilLit) rfl rfl (fun _ => rfl) rfl
  have h1 : DMethod ctx0 .ivar0 fr [.int] .int [("total", .nilT)] (.vasgn .lvar "total" (.yield' [.int 1]))
      .int [("total", .int)] := .vasgn (yield_int 1 rfl) rfl rfl (fun _ => rfl) rfl
  have h2 : DMethod ctx0 .ivar0 fr [.int] .int [("total", .int)] (.vasgn .lvar "result" (.yield' [.int 2]))
      .int [("total", .int), ("result", .int)] := .vasgn (yield_int 2 rfl) rfl rfl (fun _ => rfl) rfl
  exact .sequence (.cons h0 (.cons h1 (.cons h2 (.last (.ordinary fun _ =>
    .prim (.var rfl rfl) (.cons (.var rfl rfl) .nil rfl) .intAdd rfl (by intro h; cases h))))))

theorem nested_syntax (fr : Ratchet.Frame) :
    DMethod ctx0 .ivar0 fr [.int] .int [] nestedBody .int [("total", .int)] :=
  .yieldOne (.vasgn (yield_int 1 rfl) rfl rfl (fun _ => rfl) rfl) rfl rfl

theorem twice_syntax (fr : Ratchet.Frame) : DMethod ctx0 .ivar0 fr [.int] .int [] YieldBody.twice .int [] :=
  .prim (yield_int 1 rfl) (.cons (yield_int 2 rfl) .nil rfl) .intAdd rfl (by intro h; cases h)

theorem formatted_syntax (fr : Ratchet.Frame) : DMethod ctx0 .ivar0 fr [.int] .int [] formattedBody .int [] :=
  .prim (.prim (yield_int 1 rfl) .nil .intToS rfl (by intro h; cases h))
    .nil .strLength rfl (by intro; rfl)

theorem array_syntax (fr : Ratchet.Frame) : DMethod ctx0 .ivar0 fr [.int] .int [] arrayBody (.nilable .int) [] :=
  .prim (.ordinary fun _ => .arrayLit (.cons .intLit (.cons .intLit .nil rfl) rfl) rfl)
    (.cons (yield_int 1 rfl) .nil rfl) (.arrayIndex rfl) rfl (by intro h; cases h)

theorem divide_syntax (fr : Ratchet.Frame) : DMethod ctx0 .ivar0 fr [.int] .int [] divideBody .int [] :=
  .prim (yield_int 0 rfl) (.cons (yield_int 0 rfl) .nil rfl) .intDiv rfl (by intro h; cases h)

theorem judged (fr : Ratchet.Frame) :
    SemMethod callback fr [] mixedBody .int [("total", .int), ("result", .int)] :=
  dmethod_context (mixed_syntax fr) callback rfl rfl

theorem nested_judged (fr : Ratchet.Frame) :
    SemMethod callback fr [] nestedBody .int [("total", .int)] :=
  dmethod_context (nested_syntax fr) callback rfl rfl

/-- Rung 094's actual body now follows from general source rules. -/
theorem twice_judged (fr : Ratchet.Frame) : SemMethod callback fr [] YieldBody.twice .int [] :=
  dmethod_context (twice_syntax fr) callback rfl rfl

theorem formatted_judged (fr : Ratchet.Frame) : SemMethod callback fr [] formattedBody .int [] :=
  dmethod_context (formatted_syntax fr) callback rfl rfl

/-- The allocated array is saved while the index expression invokes a captured write. -/
theorem array_judged (fr : Ratchet.Frame) : SemMethod callback fr [] arrayBody (.nilable .int) [] :=
  dmethod_context (array_syntax fr) callback rfl rfl

theorem divide_judged (fr : Ratchet.Frame) : SemMethod callback fr [] divideBody .int [] :=
  dmethod_context (divide_syntax fr) callback rfl rfl

private def renamed : CheckedCallback ctx0 [] .ivar0 where
  code := ⟨[.req "argument"], [], .var .lvar "argument", false, rfl⟩
  params := [("argument", .int)]
  ret := .int
  names := []
  out := [("argument", .int)]
  required := rfl
  main := rfl
  returnFO := rfl
  inputTypes := rfl
  outputTypes := rfl
  fixed := rfl
  body := SemSafeCtxA.var rfl rfl

/-- The same syntactic proof instantiates at different code, names and capture environments. -/
theorem renamed_judged (fr : Ratchet.Frame) : SemMethod renamed fr [] YieldBody.twice .int [] :=
  dmethod_context (twice_syntax fr) renamed rfl rfl

private def allocated (m : Machine) : Machine := reifiedMachine m [.req "x"] [] (toRuby writeBody) false
private def method (m : Machine) (body : Ratchet.Expr) : MethodDef :=
  { params := [], body := toRuby body, owner := m.currentFrame.defmod, cref := m.currentFrame.cref }
private def callStep (m : Machine) (body : Ratchet.Expr) : StepResult :=
  let entry := allocated m
  Interp.enterUserMethod entry entry.currentFrame.self "mixed" (method entry body) []
    (some (.ref m.heap.objs.size))

private def declaration (body : Ratchet.Expr) : Defn := ⟨"mixed", [], body⟩
private def checkBody (body : Ratchet.Expr) (hint : Deriv) (ret : Ty := .int) :=
  checkCallbackBody 40 ctx0 .ivar0 (declaration body) (.defBlock "mixed" [] [.int] .int ret hint)
private def mixedChecked := (checkBody mixedBody CallbackBodyCheckControls.mixedHint).get (by decide)
private def twiceChecked := (checkBody YieldBody.twice CallbackBodyCheckControls.twiceHint).get (by decide)
private def nestedChecked := (checkBody nestedBody
  (.yieldArgs [.vasgn .lvar "total" (.yieldArgs [.intLit 1])])).get (by decide)
private def formattedChecked := (checkBody formattedBody
  (.prim (.prim (.yieldArgs [.intLit 1]) "to_s" [] .int (.cls "String"))
    "length" [] (.cls "String") .int)).get (by decide)
private def arrayChecked := (checkBody arrayBody
  (.prim (.arrayLit [.intLit 10, .intLit 20] .int) "[]" [.yieldArgs [.intLit 1]]
    (.arrayOf .int) (.nilable .int)) (.nilable .int)).get (by decide)
private def divideChecked := (checkBody divideBody
  (.prim (.yieldArgs [.intLit 0]) "/" [.yieldArgs [.intLit 0]] .int .int)).get (by decide)

theorem call {m : Machine} {body : Ratchet.Expr}
    (c : CheckedCallbackBody ctx0 .ivar0 (declaration body))
    (hp : c.params = []) (hargs : c.blockArgs = [.int]) (hret : c.blockRet = .int)
    (hm : StateOk ctx0 [("total", .int)] .ivar0 m)
    (hk : m.kont = []) (hd : CaptureSlots ["total"] [("total", .int)] m) :
    StepSpec m [("total", .int)] c.ret (callStep m body) ctx0 .ivar0 := by
  have h := checked_callback_call0 c (cb := callback) hp hargs.symm hret.symm
    (md := method (allocated m) body) (o := m.heap.objs.size)
    (cl := reifiedClosure m [.req "x"] [] (toRuby writeBody) false)
    (reified_state hm [.req "x"] [] (toRuby writeBody) false) hk rfl rfl rfl rfl rfl rfl rfl rfl
    hd (by simp only [reifiedMachine, pushHeap_get_self]) ⟨rfl, rfl, rfl, rfl⟩
  exact h.rebase (.of_ext (reified_ext hm [.req "x"] [] (toRuby writeBody) false))

private theorem call_boot {body : Ratchet.Expr}
    (c : CheckedCallbackBody ctx0 .ivar0 (declaration body))
    (hp : c.params = []) (hargs : c.blockArgs = [.int]) (hret : c.blockRet = .int)
    (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] c.ret (callStep m body) ctx0 .ivar0 := by
  have hm := stateOk_boot hb
  apply call c hp hargs hret
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
  call_boot mixedChecked rfl rfl rfl hb initial

theorem nested_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m nestedBody) ctx0 .ivar0 :=
  call_boot nestedChecked rfl rfl rfl hb initial

theorem twice_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m YieldBody.twice) ctx0 .ivar0 :=
  call_boot twiceChecked rfl rfl rfl hb initial

theorem formatted_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m formattedBody) ctx0 .ivar0 :=
  call_boot formattedChecked rfl rfl rfl hb initial

theorem array_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] (.nilable .int) (callStep m arrayBody) ctx0 .ivar0 :=
  call_boot arrayChecked rfl rfl rfl hb initial

/-- At initial=0 this raises ZeroDivisionError; that remains a typed escape. -/
theorem divide_from_boot (hb : bootOkB = true) (initial : Int) :
    let m := bootMachine.setLocal "total" (.int initial)
    StepSpec m [("total", .int)] .int (callStep m divideBody) ctx0 .ivar0 :=
  call_boot divideChecked rfl rfl rfl hb initial

#print axioms judged
#print axioms renamed_judged
#print axioms from_boot
#print axioms nested_from_boot
#print axioms twice_from_boot
#print axioms formatted_from_boot
#print axioms array_from_boot
#print axioms divide_from_boot
end Ratchet.Denote.Typed.MethodTypingControls
