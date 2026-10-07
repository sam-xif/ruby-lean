import Books.TypeSoundness.Examples.Derivations

/-! Stored non-lambda Proc calls, with independent native call/bracket dispatch guards. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

private def doubleCode : ClosureCode := ⟨[.req "x"], [],
  .send (some (.var .lvar "x")) "*" [.int 2] none, false, rfl⟩
private def procEnv : Env := [("p", .clos doubleCode .ivar0 .never)]
private def procFacts : LocalFacts := LocalFacts.unknown.write "p" true
private def procProgram (name : String) : Checker.Expr := .seq [
  .vasgn .lvar "p" (.send none "proc" [] (some (.block doubleCode.params [] doubleCode.body))),
  .send (some (.var .lvar "p")) name [.int 3] none]

private theorem proc_deriv (name : String) (hf : nameFreeN ctx0 name = true)
    (hn : procCallNameB name = true) : (DJudgeC dclinks).judge [] (procProgram name) .int procEnv := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.sequence (by simp [dclinks])
  apply hF DClink.DFlowSeq.cons (by simp [dclinks])
  · exact hF DClink.DFlow.vasgn (by simp [dclinks])
      (hF DClink.DFlow.closureLiteral (by simp [dclinks]) .unknown doubleCode rfl) rfl rfl rfl rfl
  · apply hF DClink.DFlowSeq.last (by simp [dclinks])
    apply hF DClink.DFlow.requiredCall (by simp [dclinks])
      (code := doubleCode) (ps := [("x", .int)]) (Γa := procEnv)
      (Γb := ("x", .int) :: procEnv) (names := ["p"])
      (hF DClink.DFlow.var (by simp [dclinks]) procFacts rfl rfl)
      (hF DClink.DFlowAll.cons (by simp [dclinks])
        (hF DClink.DFlow.intLit (by simp [dclinks]) procFacts 3)
        (hF DClink.DFlowAll.nil (by simp [dclinks])) rfl)
      (by intro σ h; simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; cases h; rfl)
      rfl hf rfl hn rfl rfl rfl rfl
    exact hF DClink.prim (by simp [dclinks])
      (hF DClink.var (by simp [dclinks]) rfl rfl)
      (hF DClink.DJudgeAll.cons (by simp [dclinks])
        (hF DClink.intLit (by simp [dclinks])) (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
      .intMul rfl (by intro h; cases h)

def program_089_proc_basic : Checker.Expr := procProgram "call"
def program_090_proc_bracket_call : Checker.Expr := procProgram "[]"

theorem safe_089_proc_basic (hb : bootOkB = true) : StuckFree bootMachine program_089_proc_basic :=
  dregistry_safe (proc_deriv "call" rfl rfl) (stateOk_boot hb)
theorem safe_090_proc_bracket_call (hb : bootOkB = true) :
    StuckFree bootMachine program_090_proc_bracket_call :=
  dregistry_safe (proc_deriv "[]" rfl rfl) (stateOk_boot hb)

#print axioms safe_089_proc_basic
#print axioms safe_090_proc_bracket_call
end Checker.Soundness.Typed
