import Denote.Rules.Method.BodyDefine
import Denote.Rules.Method.BodySource
import Denote.Rules.Method.BodyChecked
import Ratchet.Controls.CallbackBodyCheckControls
import Denote.Rules.Closure.FlowExpr
import Denote.Rules.Closure.FlowSequence

/-! Whole source programs: definition, installed lookup, literal block allocation,
user dispatch, repeated yields and return. No entry-state or lookup premise is supplied. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.CallbackSourceControls
open RubyCore Ratchet Ratchet.Denote

def declaration (name : String) : Defn := ⟨name, [], CallbackBodyCheckControls.twice⟩
def context (name : String) : Ctx := topDeclCtx ctx0 (declaration name)
private def check (name : String) := checkCallbackBody 30 (context name) .ivar0 (declaration name)
  (.defBlock name [] [.int] .int .int CallbackBodyCheckControls.twiceHint)

def blockBody : Ratchet.Expr := .send (some (.var .lvar "x")) "*" [.int 10] none
private def callback (name : String) (hf : nameFreeN (context name) "*" = true) :
    CheckedCallback (context name) [] .ivar0 where
  code := ⟨[.req "x"], [], blockBody, false, rfl⟩
  params := [("x", .int)]
  ret := .int
  names := []
  out := [("x", .int)]
  required := rfl
  main := rfl
  returnFO := rfl
  inputTypes := rfl
  outputTypes := rfl
  fixed := rfl
  body := (SemSafeCtxA.var rfl rfl).prim (.cons SemSafeCtxA.intLit .nil rfl)
    .intMul hf (by intro h; cases h)

def program (name : String) : Ratchet.Expr := .seq [
  .def' name [] CallbackBodyCheckControls.twice,
  .send none name [] (some (.block [.req "x"] [] blockBody))]

theorem typed (name : String) (c : CheckedCallbackBody (context name) .ivar0 (declaration name))
    (hp : c.params = []) (hargs : c.blockArgs = [.int]) (hbr : c.blockRet = .int) (hr : c.ret = .int)
    (hf : nameFreeN (context name) "*" = true)
    (hmiss : "method_missing" ≠ name) (hquiet : "method_added" ≠ name) :
    SemSafeCtxA ctx0 [] .ivar0 (program name) .int (context name) [] .ivar0 := by
  have hb : SemMethodBody (context name) .ivar0 ⟨"Object", "Object", name, false⟩
      c.blockArgs c.blockRet c.params (declaration name).body c.ret c.out := checked_callback_body_context c
  have hdef : SemSafeCtxA ctx0 [] .ivar0 (.def' name [] CallbackBodyCheckControls.twice)
      .sym (context name) [] .ivar0 :=
    SemSafeCtxA.defBlock c.paramShape c.paramsFO c.blockArgsFO c.blockReturnFO c.returnFO hb
      rfl rfl rfl rfl rfl rfl rfl (by intro p h; cases h) (by intro d h; cases h) hmiss hquiet
  rw [hp] at hb
  have hcall := (hb.callBlock (callback name hf) hargs.symm hbr.symm rfl
    (by exact List.Mem.head _) c.returnFO rfl (facts := .unknown) rfl).erase
  simpa only [hr, program, declaration, callback] using hdef.seq hcall

def checkedTwice := (check "twice").get (by decide)
def checkedLambda := (check "lambda").get (by decide)
def checkedProc := (check "proc").get (by decide)
def checkedNew := (check "new").get (by decide)

/-- Rung 094's full stripped source, now including its real def and send. -/
theorem twice_from_boot (hb : bootOkB = true) : StuckFree bootMachine (program "twice") :=
  (typed "twice" checkedTwice rfl rfl rfl rfl rfl (by decide) (by decide)).closed (stateOk_boot hb)

theorem lambda_override_from_boot (hb : bootOkB = true) : StuckFree bootMachine (program "lambda") :=
  (typed "lambda" checkedLambda rfl rfl rfl rfl rfl (by decide) (by decide)).closed (stateOk_boot hb)

theorem proc_override_from_boot (hb : bootOkB = true) : StuckFree bootMachine (program "proc") :=
  (typed "proc" checkedProc rfl rfl rfl rfl rfl (by decide) (by decide)).closed (stateOk_boot hb)

theorem new_override_from_boot (hb : bootOkB = true) : StuckFree bootMachine (program "new") :=
  (typed "new" checkedNew rfl rfl rfl rfl rfl (by decide) (by decide)).closed (stateOk_boot hb)

private def writeBody : Ratchet.Expr := .vasgn .lvar "total"
  (.send (some (.var .lvar "total")) "+" [.var .lvar "x"] none)
private def writeCallback : CheckedCallback (context "twice") [("total", .int)] .ivar0 where
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

def writeProgram (initial : Int) : Ratchet.Expr := .seq [
  .vasgn .lvar "total" (.int initial), .def' "twice" [] CallbackBodyCheckControls.twice,
  .send none "twice" [] (some (.block [.req "x"] [] writeBody)), .var .lvar "total"]

/-- Source assignment supplies physical capture ownership, through definition and dispatch. -/
theorem write_typed (initial : Int) :
    SemSafeCtxA ctx0 [] .ivar0 (writeProgram initial) .int (context "twice") [("total", .int)] .ivar0 := by
  have hb : SemMethodBody (context "twice") .ivar0 ⟨"Object", "Object", "twice", false⟩
      [.int] .int [] (declaration "twice").body .int [] := checked_callback_body_context checkedTwice
  have hi : SemFlow ctx0 [] .ivar0 .unknown (.vasgn .lvar "total" (.int initial)) .int false
      ctx0 [("total", .int)] .ivar0 (LocalFacts.unknown.write "total" false) :=
    (SemFlow.intLit .unknown initial).vasgn rfl rfl rfl rfl
  have hd : SemSafeCtxA ctx0 [("total", .int)] .ivar0 (.def' "twice" [] CallbackBodyCheckControls.twice)
      .sym (context "twice") [("total", .int)] .ivar0 :=
    SemSafeCtxA.defBlock (ps := []) rfl rfl rfl rfl rfl hb rfl rfl rfl rfl rfl rfl rfl
      (by intro p h; simp only [List.mem_singleton] at h; subst p; rfl)
      (by intro d h; cases h) (by decide) (by decide)
  have hc := hb.callBlock writeCallback rfl rfl rfl (by exact List.Mem.head _) rfl rfl
    (facts := (LocalFacts.unknown.write "total" false).afterEffect) rfl
  exact (SemFlow.sequence (.cons hi (.cons (SemFlow.embed _ hd)
    (.cons hc (.last (SemFlow.var .unknown rfl rfl)))))).erase

theorem captured_write_from_boot (hb : bootOkB = true) (initial : Int) :
    StuckFree bootMachine (writeProgram initial) := (write_typed initial).closed (stateOk_boot hb)

#print axioms twice_from_boot
#print axioms lambda_override_from_boot
#print axioms proc_override_from_boot
#print axioms new_override_from_boot
#print axioms captured_write_from_boot
end Ratchet.Denote.Typed.CallbackSourceControls
