import Denote.Examples.Derivations

/-! Worked derivations exercise flow rules through the registry's arbitrary family.
The body of a stored lambda still consumes an ordinary, registered body proof. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem derivD_flowNil : (DJudgeC dclinks).judge [] .nil .nilT [] := by
  intro F hF
  exact hF DClink.flow (by simp [dclinks]) (hF DClink.DFlow.nilLit (by simp [dclinks]) .unknown)

theorem derivD_flowReassign : (DJudgeC dclinks).judge []
    (.seq [.vasgn .lvar "x" (.int 1), .vasgn .lvar "x" .tru, .var .lvar "x"])
    .bool [("x", .bool)] := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.sequence (by simp [dclinks])
  apply hF DClink.DFlowSeq.cons (by simp [dclinks])
  · exact hF DClink.DFlow.vasgn (by simp [dclinks])
      (hF DClink.DFlow.intLit (by simp [dclinks]) .unknown 1) rfl rfl rfl rfl
  · apply hF DClink.DFlowSeq.cons (by simp [dclinks])
    · exact hF DClink.DFlow.vasgn (by simp [dclinks])
        (hF DClink.DFlow.embed (by simp [dclinks]) _
          (hF DClink.truLit (by simp [dclinks]))) rfl rfl rfl rfl
    · exact hF DClink.DFlowSeq.last (by simp [dclinks])
        (hF DClink.DFlow.var (by simp [dclinks]) _ rfl rfl)

def storedLambdaCode : ClosureCode := ⟨[], [], .int 1, true, rfl⟩
def program_087_lambda_zero_arity : Ratchet.Expr := .seq [
  .vasgn .lvar "f" (.send none "lambda" [] (some (.block [] [] (.int 1)))),
  .send (some (.var .lvar "f")) "call" [] none]

theorem derivD_storedLambda : (DJudgeC dclinks).judge [] program_087_lambda_zero_arity
    .int [("f", .clos storedLambdaCode .ivar0 .never)] := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.sequence (by simp [dclinks])
  apply hF DClink.DFlowSeq.cons (by simp [dclinks])
  · exact hF DClink.DFlow.vasgn (by simp [dclinks])
      (hF DClink.DFlow.closureLiteral (by simp [dclinks]) .unknown storedLambdaCode rfl)
      rfl rfl rfl rfl
  · apply hF DClink.DFlowSeq.last (by simp [dclinks])
    exact hF DClink.DFlow.call (by simp [dclinks])
      (facts := LocalFacts.unknown.write "f" true) (code := storedLambdaCode)
      (Γb := [("f", .clos storedLambdaCode .ivar0 .never)])
      "f" rfl rfl rfl rfl rfl (by decide) rfl rfl rfl rfl rfl
      (hF DClink.intLit (by simp [dclinks]))

theorem safe_087_lambda_zero_arity (hb : bootOkB = true) :
    StuckFree bootMachine program_087_lambda_zero_arity :=
  dregistry_safe derivD_storedLambda (stateOk_boot hb)

#print axioms derivD_storedLambda
#print axioms safe_087_lambda_zero_arity
end Ratchet.Denote.Typed
