import Books.TypeSoundness.Registry.Registry

/-! Whole-078 safety for every String argument. The singleton body is proved over
the entire String parameter domain before any call argument enters the derivation. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.ModuleParamProgram
open RubyCore Checker Checker.Soundness

def params : List SigParam := [("name", .cls "String")]
def decl : Defn := ⟨"hello", [.req "name"],
  .send (some (.str "hi ")) "+" [.var .lvar "name"] none⟩
def header : Cls := moduleHeader "Greeter"
def entry : Ctx := moduleHeaderCtx (moduleBodyCtx ctx0 "Greeter") "Greeter"
def installed : Ctx := singletonDeclCtx entry header decl
def caller : Ctx := returnScopeCtx ctx0 installed
def record : Cls := classWithSingleton header decl
def program (s : String) : Checker.Expr := .seq [
  .module' "Greeter" (.defs .self' decl.name decl.params decl.body),
  .send (some (.const "Greeter")) "hello" [.str s] none]

private theorem body_deriv {κ : Ctx} (hf : nameFreeN κ "+" = true)
    (hn : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    (DJudgeC dclinks).judge params decl.body (.cls "String") params κ .ivar0 := by
  intro F hF
  exact hF DClink.prim (by simp [dclinks]) (hF DClink.strLit (by simp [dclinks]))
    (hF DClink.DJudgeAll.cons (by simp [dclinks])
      (hF DClink.var (by simp [dclinks]) rfl rfl)
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) DPrim.strAdd hf (fun _ => hn)

theorem full_deriv (s : String) :
    (DJudgeC dclinks).judge [] (program s) (.cls "String") [] ctx0 .ivar0 caller .ivar0 := by
  intro F hF
  have definition : F.judge [] (.defs .self' decl.name decl.params decl.body) .sym []
      entry .ivar0 installed .ivar0 :=
    @hF DClink.singletonDef (by simp [dclinks]) entry [] params .ivar0 (.cls "String") header decl params
      rfl (by simp [params, FirstOrder, isAliasTy]) rfl
      (body_deriv (by decide) (by decide) F hF) (List.mem_cons_self) (by decide)
  have mod : F.judge [] (.module' "Greeter" (.defs .self' decl.name decl.params decl.body)) .sym []
      ctx0 .ivar0 caller .ivar0 := hF DClink.moduleDecl (by simp [dclinks]) definition (by decide)
  have call : F.judge [] (.send (some (.const "Greeter")) "hello" [.str s] none)
      (.cls "String") [] caller .ivar0 :=
    @hF DClink.callSingleton (by simp [dclinks]) caller caller caller
      [] [] [] params .ivar0 .ivar0 .ivar0 (.cls "String") record decl params _ _
      (@hF DClink.constClass (by simp [dclinks]) caller [] .ivar0 record (List.mem_cons_self))
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.strLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
      (List.mem_cons_self) (List.mem_cons_self) (by decide) rfl
      (by simp [params, FirstOrder, isAliasTy]) rfl
      (body_deriv (by decide) (by decide) F hF) (by decide)
  exact hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks])
    mod (hF DClink.DJudgeSeq.last (by simp [dclinks]) call))

#print axioms full_deriv
end Checker.Soundness.Typed.ModuleParamProgram

namespace Checker.Soundness.Typed
open Checker.Soundness
def program_078_module_method_with_arg : Checker.Expr := ModuleParamProgram.program "sam"
theorem safe_078_module_method_with_arg (hb : bootOkB = true) :
    StuckFree bootMachine program_078_module_method_with_arg :=
  dregistry_safe (ModuleParamProgram.full_deriv "sam") (stateOk_boot hb)
#print axioms safe_078_module_method_with_arg
end Checker.Soundness.Typed
