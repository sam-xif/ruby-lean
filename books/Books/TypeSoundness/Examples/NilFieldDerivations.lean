import Books.TypeSoundness.Registry.Registry

/-! Whole 070, with an independent derivation for any field name. Nil is an explicit
allocation fact carried in the receiver type, not a default for open instance reads. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.NilFieldProgram
open RubyCore Checker Checker.Soundness

def fields (x : String) : Ty := .ivarCons x .nilT .ivar0
def getter (x : String) : Defn := ⟨"reveal", [], .var .ivar x⟩
def header : Cls := classHeader "Box"
def entry : Ctx := classHeaderCtx (classBodyCtx ctx0 "Box") "Box"
def bodyCtx (x : String) : Ctx := instanceDeclCtx entry header (getter x)
def cls (x : String) : Cls := classWithMethod header (getter x)
def callerCtx (x : String) : Ctx := returnScopeCtx ctx0 (bodyCtx x)
def declaration (x : String) : Checker.Expr := .class' "Box" none (.def' "reveal" [] (.var .ivar x))
def newExpr : Checker.Expr := .send (some (.const "Box")) "new" [] none
def callExpr : Checker.Expr := .send (some newExpr) "reveal" [] none
def program (x : String) : Checker.Expr := .seq [declaration x, callExpr]

private theorem read_deriv (κ : Ctx) (x : String) :
    (DJudgeC dclinks).judge [] (.var .ivar x) .nilT [] κ (fields x) := by
  intro F hF
  have h := @hF DClink.ivarRead (by simp [dclinks]) κ [] (fields x) x
  simpa [Ctx.ivarReadTy, fields, ivarGet?] using h

private theorem declaration_deriv (x : String) :
    (DJudgeC dclinks).judge [] (declaration x) .sym [] ctx0 .ivar0 (callerCtx x) .ivar0 := by
  intro F hF
  apply hF DClink.classDecl (by simp [dclinks])
  · exact @hF DClink.memberDef (by simp [dclinks]) entry [] [] .ivar0 (fields x) .nilT
      header (getter x) [] rfl (by simp) rfl rfl
      (read_deriv _ x F hF) (by exact of_decide_eq_true rfl)
      (by change header ∈ [header]; simp) (by exact of_decide_eq_true rfl)
  · rfl

theorem full_deriv (x : String) :
    (DJudgeC dclinks).judge [] (program x) .nilT [] ctx0 .ivar0 (callerCtx x) .ivar0 := by
  intro F hF
  have hc : cls x ∈ (callerCtx x).classes := by
    change cls x ∈ [cls x, header]; simp
  have hn : F.judge [] newExpr (.inst "Box" (fields x)) [] (callerCtx x) .ivar0 :=
    @hF DClink.newDefault (by simp [dclinks]) (callerCtx x) (callerCtx x) (callerCtx x)
      [] [] [] .ivar0 .ivar0 .ivar0 (fields x) (cls x) (.const "Box") []
      (@hF DClink.constClass (by simp [dclinks]) (callerCtx x) [] .ivar0 (cls x) hc)
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl hc (by exact of_decide_eq_true rfl)
      (by change "Box" ∈ ["Box"]; simp) (by exact of_decide_eq_true rfl) rfl rfl
  have hg : F.judge [] callExpr .nilT [] (callerCtx x) .ivar0 :=
    @hF DClink.callMethodSig (by simp [dclinks]) (callerCtx x) (callerCtx x) (callerCtx x)
      [] [] [] [] .ivar0 .ivar0 .ivar0 (fields x) .nilT (cls x) (getter x) [] newExpr []
      hn (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl hc
      (by change getter x ∈ [getter x]; simp) (by exact of_decide_eq_true rfl)
      (by exact of_decide_eq_true rfl) rfl (by simp) rfl rfl (read_deriv _ x F hF)
      (by exact of_decide_eq_true rfl)
  exact hF DClink.seq (by simp [dclinks])
    (hF DClink.DJudgeSeq.cons (by simp [dclinks]) (declaration_deriv x F hF)
      (hF DClink.DJudgeSeq.last (by simp [dclinks]) hg))

#print axioms full_deriv
end Checker.Soundness.Typed.NilFieldProgram

namespace Checker.Soundness.Typed
open Checker.Soundness
def program_070_class_ivar_lazy_nil : Checker.Expr := NilFieldProgram.program "@secret"
theorem safe_070_class_ivar_lazy_nil (hb : bootOkB = true) : StuckFree bootMachine program_070_class_ivar_lazy_nil :=
  dregistry_safe (NilFieldProgram.full_deriv "@secret") (stateOk_boot hb)
#print axioms safe_070_class_ivar_lazy_nil
#guard match RubyCore.Interp.run 160 (evalFrom bootMachine program_070_class_ivar_lazy_nil) with
  | .value .nil _ => true
  | _ => false
end Checker.Soundness.Typed
