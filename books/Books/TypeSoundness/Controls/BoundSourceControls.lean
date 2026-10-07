import Books.TypeSoundness.Rules.Method.FlowDefine
import Books.TypeSoundness.Rules.Method.FlowSource
import Books.TypeSoundness.Rules.Method.FlowChecked
import Checker.Controls.BoundBodyCheckControls
import Books.TypeSoundness.Rules.Closure.FlowExpr
import Books.TypeSoundness.Rules.Closure.FlowSequence

/-! Whole source proofs use checked &b bodies and real definition/lookup/allocation.
No prepared entry, capture or dispatch premise is supplied by these boot controls. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.BoundSourceControls
open RubyCore Checker Checker.Soundness BoundBodyCheckControls

def declaration (name : String) (e : Checker.Expr) : Defn := ⟨name, [.block (some "b")], e⟩
def context (name : String) (e : Checker.Expr) : Ctx := topDeclCtx ctx0 (declaration name e)
private def check (name : String) (e : Checker.Expr) (d : Deriv) :=
  checkBoundCallbackBody 40 (context name e) .ivar0 (declaration name e)
    (.defBlock name [] [.int] .int .int d)

def blockBody : Checker.Expr := .send (some (.var .lvar "x")) "+" [.int 1] none
private def callback (name : String) (e : Checker.Expr) (hf : nameFreeN (context name e) "+" = true) :
    CheckedCallback (context name e) [] .ivar0 where
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
    .intAdd hf (by intro h; cases h)

def program (name : String) (e : Checker.Expr) : Checker.Expr := .seq [
  .def' name [.block (some "b")] e,
  .send none name [] (some (.block [.req "x"] [] blockBody))]

theorem typed (name : String) (e : Checker.Expr)
    (c : CheckedBoundCallbackBody (context name e) .ivar0 (declaration name e))
    (hargs : c.blockArgs = [.int]) (hbr : c.blockRet = .int) (hr : c.ret = .int)
    (hf : nameFreeN (context name e) "+" = true)
    (hcls : topDeclClassesB ctx0 name = true)
    (hmiss : "method_missing" ≠ name) (hquiet : "method_added" ≠ name) :
    SemSafeCtxA ctx0 [] .ivar0 (program name e) .int (context name e) [] .ivar0 := by
  have hb := checked_bound_callback_body_uniform c
  have hd : SemSafeCtxA ctx0 [] .ivar0 (.def' name [.block (some "b")] e)
      .sym (context name e) [] .ivar0 :=
    SemSafeCtxA.defBoundBlock c.paramShape c.blockArgsFO c.blockReturnFO c.returnFO hb
      rfl hcls rfl rfl rfl rfl rfl (by intro p h; cases h) (by intro d h; cases h) hmiss hquiet
  have hc := (SemMethodFlowBody.callBoundBlock hb (callback name e hf) hargs.symm hbr.symm c.paramShape
    (by exact List.Mem.head _) c.returnFO rfl (facts := .unknown) rfl).erase
  simpa only [hr, program, declaration, callback] using hd.seq hc

def checkedRun := (check "run" (call "b" 5) (callHint "b" 5)).get (by decide)
def checkedLambda := (check "lambda" (call "b" 5) (callHint "b" 5)).get (by decide)
def checkedProc := (check "proc" (call "b" 5) (callHint "b" 5)).get (by decide)
def checkedNew := (check "new" (call "b" 5) (callHint "b" 5)).get (by decide)

/-- Exact rung 095, with its definition and source block call. -/
theorem run_from_boot (hb : bootOkB = true) : StuckFree bootMachine (program "run" (call "b" 5)) :=
  (typed "run" _ checkedRun rfl rfl rfl rfl (by decide) (by decide) (by decide)).closed (stateOk_boot hb)

theorem lambda_override_from_boot (hb : bootOkB = true) :
    StuckFree bootMachine (program "lambda" (call "b" 5)) :=
  (typed "lambda" _ checkedLambda rfl rfl rfl rfl (by decide) (by decide) (by decide)).closed (stateOk_boot hb)

theorem proc_override_from_boot (hb : bootOkB = true) :
    StuckFree bootMachine (program "proc" (call "b" 5)) :=
  (typed "proc" _ checkedProc rfl rfl rfl rfl (by decide) (by decide) (by decide)).closed (stateOk_boot hb)

theorem new_override_from_boot (hb : bootOkB = true) :
    StuckFree bootMachine (program "new" (call "b" 5)) :=
  (typed "new" _ checkedNew rfl rfl rfl rfl (by decide) (by decide) (by decide)).closed (stateOk_boot hb)

private def writeBody : Checker.Expr := .vasgn .lvar "total"
  (.send (some (.var .lvar "total")) "+" [.var .lvar "value"] none)
private def writeCallback (e : Checker.Expr) : CheckedCallback (context "run" e) [("total", .int)] .ivar0 where
  code := ⟨[.req "value"], [], writeBody, false, rfl⟩
  params := [("value", .int)]
  ret := .int
  names := ["total"]
  out := [("value", .int), ("total", .int)]
  required := rfl
  main := rfl
  returnFO := rfl
  inputTypes := rfl
  outputTypes := rfl
  fixed := rfl
  body := ((SemSafeCtxA.var rfl rfl).prim (.cons (SemSafeCtxA.var rfl rfl) .nil rfl)
    .intAdd rfl (by intro h; cases h)).vasgn rfl rfl rfl

def writeProgram (e : Checker.Expr) (initial : Int) : Checker.Expr := .seq [
  .vasgn .lvar "total" (.int initial), .def' "run" [.block (some "b")] e,
  .send none "run" [] (some (.block [.req "value"] [] writeBody)), .var .lvar "total"]

theorem write_typed (e : Checker.Expr)
    (c : CheckedBoundCallbackBody (context "run" e) .ivar0 (declaration "run" e))
    (hargs : c.blockArgs = [.int]) (hbr : c.blockRet = .int) (initial : Int) :
    SemSafeCtxA ctx0 [] .ivar0 (writeProgram e initial) .int (context "run" e) [("total", .int)] .ivar0 := by
  have hb := checked_bound_callback_body_uniform c
  have hi : SemFlow ctx0 [] .ivar0 .unknown (.vasgn .lvar "total" (.int initial)) .int false
      ctx0 [("total", .int)] .ivar0 (LocalFacts.unknown.write "total" false) :=
    (SemFlow.intLit .unknown initial).vasgn rfl rfl rfl rfl
  have hd : SemSafeCtxA ctx0 [("total", .int)] .ivar0 (.def' "run" [.block (some "b")] e)
      .sym (context "run" e) [("total", .int)] .ivar0 :=
    SemSafeCtxA.defBoundBlock c.paramShape c.blockArgsFO c.blockReturnFO c.returnFO hb
      rfl (by change topDeclClassesB ctx0 "run" = true; decide) rfl rfl rfl rfl rfl
      (by intro p h; simp only [List.mem_singleton] at h; subst p; rfl)
      (by intro d h; cases h) (by change "method_missing" ≠ "run"; decide)
      (by change "method_added" ≠ "run"; decide)
  have hc := SemMethodFlowBody.callBoundBlock hb (writeCallback e) hargs.symm hbr.symm c.paramShape
    (by exact List.Mem.head _) c.returnFO rfl
    (facts := (LocalFacts.unknown.write "total" false).afterEffect) rfl
  exact (SemFlow.sequence (.cons hi (.cons (SemFlow.embed _ hd)
    (.cons hc (.last (SemFlow.var .unknown rfl rfl)))))).erase

def checkedCopied := (check "run" copiedBody copiedHint).get (by decide)
def checkedRestored := (check "run" restoredBody restoredHint).get (by decide)
def checkedReceiver := (check "run" receiverBody receiverHint).get (by decide)
def checkedSaved := (check "run" savedBody savedHint).get (by decide)

theorem copied_write_from_boot (hb : bootOkB = true) (initial : Int) :
    StuckFree bootMachine (writeProgram copiedBody initial) :=
  (write_typed _ checkedCopied rfl rfl initial).closed (stateOk_boot hb)
theorem restored_write_from_boot (hb : bootOkB = true) (initial : Int) :
    StuckFree bootMachine (writeProgram restoredBody initial) :=
  (write_typed _ checkedRestored rfl rfl initial).closed (stateOk_boot hb)
theorem receiver_write_from_boot (hb : bootOkB = true) (initial : Int) :
    StuckFree bootMachine (writeProgram receiverBody initial) :=
  (write_typed _ checkedReceiver rfl rfl initial).closed (stateOk_boot hb)
theorem saved_write_from_boot (hb : bootOkB = true) (initial : Int) :
    StuckFree bootMachine (writeProgram savedBody initial) :=
  (write_typed _ checkedSaved rfl rfl initial).closed (stateOk_boot hb)

#print axioms run_from_boot
#print axioms lambda_override_from_boot
#print axioms proc_override_from_boot
#print axioms new_override_from_boot
#print axioms copied_write_from_boot
#print axioms restored_write_from_boot
#print axioms receiver_write_from_boot
#print axioms saved_write_from_boot
end Checker.Soundness.Typed.BoundSourceControls
