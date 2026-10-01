import Denote.Rules.Closure.FlowExpr
import Denote.Rules.Closure.FlowCall
import Denote.Rules.Closure.FlowSequence

/-! Whole-source controls compose the same local-flow contracts intended for the
checker, starting without any assumption about the caller's hidden local slots. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ClosureFlowControls
open RubyCore Ratchet Ratchet.Denote

private def code : ClosureCode := ⟨[], [], .int 1, true, rfl⟩
private def literal : Ratchet.Expr := .send none "lambda" [] (some (.block [] [] (.int 1)))
private def fEnv : Env := [("f", .clos code .ivar0 .never)]
private def fFacts : LocalFacts := LocalFacts.unknown.write "f" true
private def aliases : Env := fEnv ++ [("g", .clos code .ivar0 .never)]
private def aliasFacts : LocalFacts := fFacts.write "g" true
private def overwritten : Env := [("f", .nilT), ("g", .clos code .ivar0 .never)]
private def overwrittenFacts : LocalFacts := aliasFacts.write "f" false

private theorem store : SemFlow ctx0 [] .ivar0 .unknown (.vasgn .lvar "f" literal)
    (.clos code .ivar0 .never) true ctx0 fEnv .ivar0 fFacts :=
  SemFlow.vasgn (SemFlow.closureLiteral .unknown code rfl) rfl rfl rfl rfl

theorem stored_call : SemSafeCtxA ctx0 [] .ivar0
    (.seq [.vasgn .lvar "f" literal, .send (some (.var .lvar "f")) "call" [] none])
    .int ctx0 fEnv .ivar0 := by
  apply SemFlow.erase
  apply SemFlow.sequence
  apply SemFlowSeq.cons store
  exact .last (SemFlow.call (facts := fFacts) (code := code) (Γb := fEnv)
    "f" rfl rfl rfl rfl rfl (by decide) rfl rfl rfl rfl rfl
    SemSafeCtxA.intLit)

private theorem copy : SemFlow ctx0 fEnv .ivar0 fFacts (.vasgn .lvar "g" (.var .lvar "f"))
    (.clos code .ivar0 .never) true ctx0 aliases .ivar0 aliasFacts :=
  SemFlow.vasgn (SemFlow.var fFacts rfl rfl) rfl rfl rfl rfl

private theorem overwrite : SemFlow ctx0 aliases .ivar0 aliasFacts (.vasgn .lvar "f" .nil)
    .nilT false ctx0 overwritten .ivar0 overwrittenFacts :=
  SemFlow.vasgn (SemFlow.nilLit aliasFacts) rfl rfl rfl rfl

theorem copied_call : SemSafeCtxA ctx0 [] .ivar0
    (.seq [.vasgn .lvar "f" literal, .vasgn .lvar "g" (.var .lvar "f"),
      .vasgn .lvar "f" .nil, .send (some (.var .lvar "g")) "call" [] none])
    .int ctx0 overwritten .ivar0 := by
  apply SemFlow.erase
  apply SemFlow.sequence
  apply SemFlowSeq.cons store
  apply SemFlowSeq.cons copy
  apply SemFlowSeq.cons overwrite
  exact .last (SemFlow.call (facts := overwrittenFacts) (code := code) (Γb := overwritten)
    "g" rfl rfl rfl rfl rfl (by decide) rfl rfl rfl rfl rfl
    SemSafeCtxA.intLit)

-- Known-bound slots suffice even when the caller's full slot domain is unknown.
#guard fFacts.slots == none
#guard fFacts.captureNames? fEnv == some ["f"]
#guard fFacts.captureNames? [("missing", .int)] == none
#guard overwrittenFacts.currentProcs == ["g"]
#guard !activationStableB (.clos code (envToSpine [("x", .int)]) .never)

#print axioms stored_call
#print axioms copied_call
end Ratchet.Denote.Typed.ClosureFlowControls
