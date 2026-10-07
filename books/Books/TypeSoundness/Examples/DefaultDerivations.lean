import Books.TypeSoundness.Registry.Registry

/-! Whole 066, with an independently audited derivation and a parameterized override. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.DefaultInheritance
open RubyCore Checker Checker.Soundness

def speak (s : String) : Defn := ⟨"speak", [], .str s⟩
def baseHeader : Cls := classHeader "Animal"
def baseEntry : Ctx := classHeaderCtx (classBodyCtx ctx0 "Animal") "Animal"
def baseBody : Ctx := instanceDeclCtx baseEntry baseHeader (speak "...")
def base : Cls := classWithMethod baseHeader (speak "...")
def baseCtx : Ctx := returnScopeCtx ctx0 baseBody
def childHeader : Cls := subclassHeader "Dog" "Animal"
def childEntry : Ctx := subclassHeaderCtx (classBodyCtx baseCtx "Dog") "Dog" "Animal"
def childBody (s : String) : Ctx := instanceDeclCtx childEntry childHeader (speak s)
def child (s : String) : Cls := classWithMethod childHeader (speak s)
def callerCtx (s : String) : Ctx := returnScopeCtx baseCtx (childBody s)
def baseExpr : Checker.Expr := .class' "Animal" none (.def' "speak" [] (.str "..."))
def childExpr (s : String) : Checker.Expr := .class' "Dog" (some (.const "Animal"))
  (.def' "speak" [] (.str s))
def newExpr : Checker.Expr := .send (some (.const "Dog")) "new" [] none
def callExpr : Checker.Expr := .send (some newExpr) "speak" [] none
def program (s : String) : Checker.Expr := .seq [baseExpr, childExpr s, callExpr]

private theorem base_deriv :
    (DJudgeC dclinks).judge [] baseExpr .sym [] ctx0 .ivar0 baseCtx .ivar0 := by
  intro F hF
  apply hF DClink.classDecl (by simp [dclinks])
  · exact @hF DClink.memberDef (by simp [dclinks]) baseEntry [] [] .ivar0 .ivar0 (.cls "String")
      baseHeader (speak "...") [] rfl (by simp) rfl rfl
      (hF DClink.strLit (by simp [dclinks])) (by exact of_decide_eq_true rfl)
      (by change baseHeader ∈ [baseHeader]; simp) (by exact of_decide_eq_true rfl)
  · rfl

private theorem child_deriv (s : String) :
    (DJudgeC dclinks).judge [] (childExpr s) .sym [] baseCtx .ivar0 (callerCtx s) .ivar0 := by
  intro F hF
  apply @hF DClink.subclassDecl (by simp [dclinks]) baseCtx baseCtx (childBody s)
    [] [] [] .ivar0 .ivar0 .ivar0 .sym base "Dog" (.const "Animal") (.def' "speak" [] (.str s))
  · exact @hF DClink.constClass (by simp [dclinks]) baseCtx [] .ivar0 base (by
      change base ∈ [base, baseHeader]; simp)
  · change base ∈ [base, baseHeader]; simp
  · exact @hF DClink.memberDef (by simp [dclinks]) childEntry [] [] .ivar0 .ivar0 (.cls "String")
      childHeader (speak s) [] rfl (by simp) rfl rfl
      (hF DClink.strLit (by simp [dclinks])) (by exact of_decide_eq_true rfl)
      (by change childHeader ∈ [childHeader, base, baseHeader]; simp) (by exact of_decide_eq_true rfl)
  · rfl

theorem full_deriv (s : String) :
    (DJudgeC dclinks).judge [] (program s) (.cls "String") [] ctx0 .ivar0 (callerCtx s) .ivar0 := by
  intro F hF
  have hc : child s ∈ (callerCtx s).classes := by
    change child s ∈ [child s, childHeader, base, baseHeader]; simp
  have hn : F.judge [] newExpr (.inst "Dog" .ivar0) [] (callerCtx s) .ivar0 :=
    @hF DClink.newDefault (by simp [dclinks]) (callerCtx s) (callerCtx s) (callerCtx s)
      [] [] [] .ivar0 .ivar0 .ivar0 .ivar0 (child s) (.const "Dog") []
      (@hF DClink.constClass (by simp [dclinks]) (callerCtx s) [] .ivar0 (child s) hc)
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl hc (by exact of_decide_eq_true rfl)
      (by change "Dog" ∈ ["Dog", "Animal"]; simp) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) rfl
  have hg : F.judge [] callExpr (.cls "String") [] (callerCtx s) .ivar0 :=
    @hF DClink.callMethodSig (by simp [dclinks]) (callerCtx s) (callerCtx s) (callerCtx s)
      [] [] [] [] .ivar0 .ivar0 .ivar0 .ivar0 (.cls "String") (child s) (speak s) [] newExpr []
      hn (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl hc
      (by change speak s ∈ [speak s]; simp) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) rfl (by simp) rfl rfl
      (hF DClink.strLit (by simp [dclinks])) (by exact of_decide_eq_true rfl)
  exact hF DClink.seq (by simp [dclinks])
    (hF DClink.DJudgeSeq.cons (by simp [dclinks]) (base_deriv F hF)
      (hF DClink.DJudgeSeq.cons (by simp [dclinks]) (child_deriv s F hF)
        (hF DClink.DJudgeSeq.last (by simp [dclinks]) hg)))

#print axioms full_deriv
end Checker.Soundness.Typed.DefaultInheritance

namespace Checker.Soundness.Typed
open Checker.Soundness
def program_066_class_inheritance_override : Checker.Expr := DefaultInheritance.program "Woof"
theorem safe_066_class_inheritance_override (hb : bootOkB = true) :
    StuckFree bootMachine program_066_class_inheritance_override :=
  dregistry_safe (DefaultInheritance.full_deriv "Woof") (stateOk_boot hb)
#print axioms safe_066_class_inheritance_override
#guard match RubyCore.Interp.run 200 (evalFrom bootMachine program_066_class_inheritance_override) with
  | .value v m => RubyCore.Builtins.strPayload? m.heap v == some "Woof"
  | _ => false
end Checker.Soundness.Typed
