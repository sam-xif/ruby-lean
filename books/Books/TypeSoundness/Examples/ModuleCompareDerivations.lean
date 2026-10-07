import Books.TypeSoundness.Registry.Registry

/-! Whole-084 safety for every Integer argument. The singleton body is proved over
the entire Integer parameter domain before any call argument enters the derivation. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.ModuleCompareProgram
open RubyCore Checker Checker.Soundness

def params : List SigParam := [("n", .int)]
def decl : Defn := ⟨"positive?", [.req "n"],
  .send (some (.var .lvar "n")) ">" [.int 0] none⟩
def header : Cls := moduleHeader "M"
def entry : Ctx := moduleHeaderCtx (moduleBodyCtx ctx0 "M") "M"
def installed : Ctx := singletonDeclCtx entry header decl
def caller : Ctx := returnScopeCtx ctx0 installed
def record : Cls := classWithSingleton header decl
def program (n : Int) : Checker.Expr := .seq [
  .module' "M" (.defs .self' decl.name decl.params decl.body),
  .send (some (.const "M")) "positive?" [.int n] none]

private theorem body_deriv {κ : Ctx} (hf : nameFreeN κ ">" = true) :
    (DJudgeC dclinks).judge params decl.body .bool params κ .ivar0 := by
  intro F hF
  exact hF DClink.prim (by simp [dclinks])
    (hF DClink.var (by simp [dclinks]) rfl rfl)
    (hF DClink.DJudgeAll.cons (by simp [dclinks])
      (hF DClink.intLit (by simp [dclinks]))
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) DPrim.intGt hf (by intro h; cases h)

theorem full_deriv (n : Int) :
    (DJudgeC dclinks).judge [] (program n) .bool [] ctx0 .ivar0 caller .ivar0 := by
  intro F hF
  have definition : F.judge [] (.defs .self' decl.name decl.params decl.body) .sym []
      entry .ivar0 installed .ivar0 :=
    @hF DClink.singletonDef (by simp [dclinks]) entry [] params .ivar0 .bool header decl params
      rfl (by simp [params, FirstOrder, isAliasTy]) rfl
      (body_deriv (by decide) F hF) (List.mem_cons_self) (by decide)
  have mod : F.judge [] (.module' "M" (.defs .self' decl.name decl.params decl.body)) .sym []
      ctx0 .ivar0 caller .ivar0 := hF DClink.moduleDecl (by simp [dclinks]) definition (by decide)
  have call : F.judge [] (.send (some (.const "M")) "positive?" [.int n] none)
      .bool [] caller .ivar0 :=
    @hF DClink.callSingleton (by simp [dclinks]) caller caller caller
      [] [] [] params .ivar0 .ivar0 .ivar0 .bool record decl params _ _
      (@hF DClink.constClass (by simp [dclinks]) caller [] .ivar0 record (List.mem_cons_self))
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
      (List.mem_cons_self) (List.mem_cons_self) (by decide) rfl
      (by simp [params, FirstOrder, isAliasTy]) rfl
      (body_deriv (by decide) F hF) (by decide)
  exact hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks])
    mod (hF DClink.DJudgeSeq.last (by simp [dclinks]) call))

#print axioms full_deriv
end Checker.Soundness.Typed.ModuleCompareProgram

namespace Checker.Soundness.Typed
open Checker.Soundness
def program_084_module_boolean_method : Checker.Expr := ModuleCompareProgram.program 5
theorem safe_084_module_boolean_method (hb : bootOkB = true) :
    StuckFree bootMachine program_084_module_boolean_method :=
  dregistry_safe (ModuleCompareProgram.full_deriv 5) (stateOk_boot hb)
#print axioms safe_084_module_boolean_method
end Checker.Soundness.Typed
