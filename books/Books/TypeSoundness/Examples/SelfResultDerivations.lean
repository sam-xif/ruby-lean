import Books.TypeSoundness.Registry.Registry

/-! Independent whole-076 derivation. Definition checks the nominal annotation; the call
uses the separately proved initialized-instance result for every Integer input. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.SelfResultProgram
open RubyCore Checker Checker.Soundness

def fields : Ty := .ivarCons "@x" .int .ivar0
def params : List SigParam := [("x", .int)]
def init : Defn := ⟨"initialize", [.req "x"], .vasgn .ivar "@x" (.var .lvar "x")⟩
def getter : Defn := ⟨"getX", [], .var .ivar "@x"⟩
def myself : Defn := ⟨"myself", [], .self'⟩
def header : Cls := classHeader "Point"
def entry : Ctx := classHeaderCtx (classBodyCtx ctx0 "Point") "Point"
def withInit : Cls := classWithMethod header init
def afterInit : Ctx := instanceDeclCtx entry header init
def withGetter : Cls := classWithMethod withInit getter
def afterGetter : Ctx := instanceDeclCtx afterInit withInit getter
def fullClass : Cls := classWithMethod withGetter myself
def afterMyself : Ctx := instanceDeclCtx afterGetter withGetter myself
def caller : Ctx := returnScopeCtx ctx0 afterMyself
def declaration : Checker.Expr := .class' "Point" none (.seq [
  .def' init.name init.params init.body, .def' getter.name getter.params getter.body,
  .def' myself.name myself.params myself.body])
def newExpr (n : Int) : Checker.Expr := .send (some (.const "Point")) "new" [.int n] none
def myselfExpr (n : Int) : Checker.Expr := .send (some (newExpr n)) "myself" [] none
def program (n : Int) : Checker.Expr :=
  .seq [declaration, .send (some (myselfExpr n)) "getX" [] none]

private theorem init_deriv {κ : Ctx} (hs : κ.selfTy = some (.inst "Point" .ivar0))
    (hb : κ.blockTy = none) (hc : κ.consts = []) :
    (DJudgeC dclinks).init κ params .ivar0 init.body .any κ params fields := by
  intro F hF
  exact hF DClink.InitJudge.ignoreResult (by simp [dclinks])
    (hF DClink.InitJudge.ivarAsgn (by simp [dclinks])
      (hF DClink.InitJudge.var (by simp [dclinks]) rfl rfl) (by
        simp [writeTypesB, params, IvarStable, stripAlias, writeFieldsB, spineKeys, hs, hb, hc]))

private theorem declaration_deriv :
    (DJudgeC dclinks).judge [] declaration .sym [] ctx0 .ivar0 caller .ivar0 := by
  intro F hF
  have hi : F.judge [] (.def' init.name init.params init.body) .sym [] entry .ivar0 afterInit .ivar0 :=
    @hF DClink.initDef (by simp [dclinks]) entry [] params .ivar0 fields .any header init params
      rfl rfl (by simp [params, FirstOrder, isAliasTy]) rfl rfl (init_deriv rfl rfl rfl F hF)
      (by change header ∈ [header]; simp) (by decide)
  have hg : F.judge [] (.def' getter.name getter.params getter.body) .sym [] afterInit .ivar0 afterGetter .ivar0 :=
    @hF DClink.memberDef (by simp [dclinks]) afterInit [] [] .ivar0 fields .int withInit getter []
      rfl (by simp) rfl rfl
      (@hF DClink.ivarRead (by simp [dclinks])
        (instanceBodyCtx afterGetter ⟨"Point", "Point", "getX", false⟩ fields) [] fields "@x") (by decide)
      (by change withInit ∈ [withInit, header]; simp) (by decide)
  have hm : F.judge [] (.def' myself.name myself.params myself.body) .sym [] afterGetter .ivar0 afterMyself .ivar0 :=
    @hF DClink.memberDef (by simp [dclinks]) afterGetter [] [] .ivar0 fields (.cls "Point") withGetter myself []
      rfl (by simp) rfl rfl
      (@hF DClink.instanceType (by simp [dclinks])
        (instanceBodyCtx afterMyself ⟨"Point", "Point", "myself", false⟩ fields)
        (instanceBodyCtx afterMyself ⟨"Point", "Point", "myself", false⟩ fields)
        [] [] fields fields fields fullClass .self'
        (hF DClink.selfRead (by simp [dclinks]) rfl)
        (by change fullClass ∈ [fullClass, withGetter, withInit, header]; simp)) (by decide)
      (by change withGetter ∈ [withGetter, withInit, header]; simp) (by decide)
  exact hF DClink.classDecl (by simp [dclinks])
    (hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hi
      (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hg
        (hF DClink.DJudgeSeq.last (by simp [dclinks]) hm)))) (by decide)

theorem full_deriv (n : Int) :
    (DJudgeC dclinks).judge [] (program n) .int [] ctx0 .ivar0 caller .ivar0 := by
  intro F hF
  have hc : fullClass ∈ caller.classes := by change fullClass ∈ [fullClass, withGetter, withInit, header]; simp
  have hn : F.judge [] (newExpr n) (.inst "Point" fields) [] caller .ivar0 :=
    @hF DClink.newInst (by simp [dclinks]) caller caller caller [] [] [] params
      .ivar0 .ivar0 .ivar0 fields .any fullClass init params _ _
      (hF DClink.constClass (by simp [dclinks]) hc)
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) rfl hc
      (by change init ∈ [myself, getter, init]; simp) rfl (by decide)
      (by change "Point" ∈ ["Point"]; simp) rfl (by simp [params, FirstOrder, isAliasTy])
      rfl rfl (init_deriv rfl rfl rfl F hF) (by decide)
  have hm : F.judge [] (myselfExpr n) (.inst "Point" fields) [] caller .ivar0 :=
    @hF DClink.callMethodSig (by simp [dclinks]) caller caller caller [] [] [] []
      .ivar0 .ivar0 .ivar0 fields (.inst "Point" fields) fullClass myself [] _ _ hn
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl hc
      (by change myself ∈ [myself, getter, init]; simp) (by decide) (by decide) rfl (by simp) rfl rfl
      (hF DClink.selfRead (by simp [dclinks]) rfl) (by decide)
  have hg : F.judge [] (.send (some (myselfExpr n)) "getX" [] none) .int [] caller .ivar0 :=
    @hF DClink.callMethodSig (by simp [dclinks]) caller caller caller [] [] [] []
      .ivar0 .ivar0 .ivar0 fields .int fullClass getter [] _ _ hm
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl hc
      (by change getter ∈ [myself, getter, init]; simp) (by decide) (by decide) rfl (by simp) rfl rfl
      (@hF DClink.ivarRead (by simp [dclinks])
        (instanceBodyCtx caller ⟨"Point", "Point", "getX", false⟩ fields) [] fields "@x") (by decide)
  exact hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks])
    (declaration_deriv F hF) (hF DClink.DJudgeSeq.last (by simp [dclinks]) hg))

#print axioms full_deriv
end Checker.Soundness.Typed.SelfResultProgram

namespace Checker.Soundness.Typed
open Checker.Soundness
def program_076_class_self_returning_method : Checker.Expr := SelfResultProgram.program 7
theorem safe_076_class_self_returning_method (hb : bootOkB = true) :
    StuckFree bootMachine program_076_class_self_returning_method :=
  dregistry_safe (SelfResultProgram.full_deriv 7) (stateOk_boot hb)
#guard match RubyCore.Interp.run 500 (evalFrom bootMachine program_076_class_self_returning_method) with
  | .value (.int 7) _ => true
  | _ => false
#print axioms safe_076_class_self_returning_method
end Checker.Soundness.Typed
