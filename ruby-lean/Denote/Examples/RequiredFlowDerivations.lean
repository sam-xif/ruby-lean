import Denote.Examples.Derivations

/-! Required-lambda examples derive every receiver, argument and body premise through
the arbitrary registry family. Capture types are checked when the body is invoked. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def incrementLambdaCode : ClosureCode := ⟨[.req "x"], [],
  .send (some (.var .lvar "x")) "+" [.int 1] none, true, rfl⟩
def program_088_lambda_stabby_one_param : Ratchet.Expr := .send
  (some (.send none "lambda" [] (some (.block incrementLambdaCode.params [] incrementLambdaCode.body))))
  "call" [.int 2] none

theorem derivD_requiredLambda : (DJudgeC dclinks).judge [] program_088_lambda_stabby_one_param
    .int [] := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.requiredCall (by simp [dclinks])
    (ps := [("x", .int)]) (Γb := [("x", .int)])
    (hF DClink.DFlow.closureLiteral (by simp [dclinks]) .unknown incrementLambdaCode rfl)
    (hF DClink.DFlowAll.cons (by simp [dclinks])
      (hF DClink.DFlow.intLit (by simp [dclinks]) .unknown 2)
      (hF DClink.DFlowAll.nil (by simp [dclinks])) rfl)
    (by intro σ h; simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; cases h; rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl
  exact hF DClink.prim (by simp [dclinks])
    (hF DClink.var (by simp [dclinks]) rfl rfl)
    (hF DClink.DJudgeAll.cons (by simp [dclinks])
      (hF DClink.intLit (by simp [dclinks])) (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
    .intAdd rfl (by intro h; cases h)

def capturedLambdaCode : ClosureCode := ⟨[.req "x"], [],
  .send (some (.var .lvar "x")) "+" [.var .lvar "n"] none, true, rfl⟩
private def capturedEnv : Env := [("n", .int), ("add_n", .clos capturedLambdaCode .ivar0 .never)]
private def capturedFacts : LocalFacts := (LocalFacts.unknown.write "n" false).write "add_n" true
def program_098_lambda_closure_capture : Ratchet.Expr := .seq [
  .vasgn .lvar "n" (.int 10),
  .vasgn .lvar "add_n" (.send none "lambda" []
    (some (.block capturedLambdaCode.params [] capturedLambdaCode.body))),
  .send (some (.var .lvar "add_n")) "call" [.int 5] none]

theorem derivD_capturedLambda : (DJudgeC dclinks).judge [] program_098_lambda_closure_capture
    .int capturedEnv := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.sequence (by simp [dclinks])
  apply hF DClink.DFlowSeq.cons (by simp [dclinks])
  · exact hF DClink.DFlow.vasgn (by simp [dclinks])
      (hF DClink.DFlow.intLit (by simp [dclinks]) .unknown 10) rfl rfl rfl rfl
  · apply hF DClink.DFlowSeq.cons (by simp [dclinks])
    · exact hF DClink.DFlow.vasgn (by simp [dclinks])
        (hF DClink.DFlow.closureLiteral (by simp [dclinks]) _ capturedLambdaCode rfl)
        rfl rfl rfl rfl
    · apply hF DClink.DFlowSeq.last (by simp [dclinks])
      apply hF DClink.DFlow.requiredCall (by simp [dclinks])
        (code := capturedLambdaCode) (ps := [("x", .int)])
        (Γa := capturedEnv) (Γb := ("x", .int) :: capturedEnv) (names := ["add_n", "n"])
        (hF DClink.DFlow.var (by simp [dclinks]) capturedFacts rfl rfl)
        (hF DClink.DFlowAll.cons (by simp [dclinks])
          (hF DClink.DFlow.intLit (by simp [dclinks]) capturedFacts 5)
          (hF DClink.DFlowAll.nil (by simp [dclinks])) rfl)
        (by intro σ h; simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; cases h; rfl)
        rfl rfl rfl rfl rfl rfl rfl rfl
      exact hF DClink.prim (by simp [dclinks])
        (hF DClink.var (by simp [dclinks]) rfl rfl)
        (hF DClink.DJudgeAll.cons (by simp [dclinks])
          (hF DClink.var (by simp [dclinks]) rfl rfl)
          (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
        .intAdd rfl (by intro h; cases h)

theorem safe_088_lambda_stabby_one_param (hb : bootOkB = true) :
    StuckFree bootMachine program_088_lambda_stabby_one_param :=
  dregistry_safe derivD_requiredLambda (stateOk_boot hb)
theorem safe_098_lambda_closure_capture (hb : bootOkB = true) :
    StuckFree bootMachine program_098_lambda_closure_capture :=
  dregistry_safe derivD_capturedLambda (stateOk_boot hb)

#print axioms safe_088_lambda_stabby_one_param
#print axioms safe_098_lambda_closure_capture
end Ratchet.Denote.Typed
