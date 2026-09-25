import Denote.Clink.Registry

/-! Whole 075, derived independently at every Integer constructor argument. The top-level
body is checked for every receiver in its declared initialized-instance domain. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.TopClassProgram
open RubyCore Ratchet Ratchet.Denote

def fields : Ty := .ivarCons "@x" .int .ivar0
def params : List SigParam := [("x", .int)]
def init : Defn := ⟨"initialize", [.req "x"], .vasgn .ivar "@x" (.var .lvar "x")⟩
def getter : Defn := ⟨"getX", [], .var .ivar "@x"⟩
def header : Cls := classHeader "Point"
def entry : Ctx := classHeaderCtx (classBodyCtx ctx0 "Point") "Point"
def withInit : Cls := classWithMethod header init
def afterInit : Ctx := instanceDeclCtx entry header init
def fullClass : Cls := classWithMethod withInit getter
def afterGetter : Ctx := instanceDeclCtx afterInit withInit getter
def afterClass : Ctx := returnScopeCtx ctx0 afterGetter
def reader : Defn := ⟨"describe", [.req "p"], .send (some (.var .lvar "p")) "getX" [] none⟩
def readerParams : List SigParam := [("p", .inst "Point" fields)]
def caller : Ctx := topDeclCtx afterClass reader
def bodyCtx : Ctx := topBodyCtx afterClass reader
def declaration : Ratchet.Expr := .class' "Point" none (.seq [
  .def' init.name init.params init.body, .def' getter.name getter.params getter.body])
def newExpr (n : Int) : Ratchet.Expr := .send (some (.const "Point")) "new" [.int n] none
def callExpr (n : Int) : Ratchet.Expr := .send none "describe" [newExpr n] none
def program (n : Int) : Ratchet.Expr :=
  .seq [declaration, .def' reader.name reader.params reader.body, callExpr n]

private theorem init_deriv {κ : Ctx} (hs : κ.selfTy = some (.inst "Point" .ivar0))
    (hb : κ.blockTy = none) (hc : κ.consts = []) :
    (DJudgeC dclinks).init κ params .ivar0 init.body .any κ params fields := by
  intro F hF
  exact hF DClink.InitJudge.ignoreResult (by simp [dclinks])
    (hF DClink.InitJudge.ivarAsgn (by simp [dclinks])
      (hF DClink.InitJudge.var (by simp [dclinks]) rfl rfl) (by
        simp [writeTypesB, params, IvarStable, stripAlias, writeFieldsB, spineKeys, hs, hb, hc]))

private theorem declaration_deriv :
    (DJudgeC dclinks).judge [] declaration .sym [] ctx0 .ivar0 afterClass .ivar0 := by
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
  exact hF DClink.classDecl (by simp [dclinks])
    (hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hi
      (hF DClink.DJudgeSeq.last (by simp [dclinks]) hg))) (by decide)

private theorem reader_deriv :
    (DJudgeC dclinks).judge readerParams reader.body .int readerParams bodyCtx .ivar0 := by
  intro F hF
  exact @hF DClink.callMethodSig (by simp [dclinks]) bodyCtx bodyCtx bodyCtx
    readerParams readerParams readerParams [] .ivar0 .ivar0 .ivar0 fields .int fullClass getter [] _ _
    (hF DClink.var (by simp [dclinks]) rfl rfl) (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl
    (by change fullClass ∈ [fullClass, withInit, header]; simp)
    (by change getter ∈ [getter, init]; simp) (by decide) (by decide) rfl (by simp) rfl rfl
    (@hF DClink.ivarRead (by simp [dclinks])
      (instanceBodyCtx bodyCtx ⟨"Point", "Point", "getX", false⟩ fields) [] fields "@x") (by decide)

theorem full_deriv (n : Int) :
    (DJudgeC dclinks).judge [] (program n) .int [] ctx0 .ivar0 caller .ivar0 := by
  intro F hF
  have hd : F.judge [] (.def' reader.name reader.params reader.body) .sym [] afterClass .ivar0 caller .ivar0 :=
    hF DClink.defDecl (by simp [dclinks]) rfl
      (by simp [readerParams, FirstOrder, fields, isAliasTy]) rfl (reader_deriv F hF)
      rfl (by decide) rfl rfl rfl rfl rfl (by simp) (by simp [afterClass, Ctx.defs,
        returnScopeCtx, afterGetter, afterInit, entry, instanceDeclCtx, classHeaderCtx, classBodyCtx,
        reserveNameCtx, ctx0]) (by decide) (by decide)
  have hc : fullClass ∈ caller.classes := by change fullClass ∈ [fullClass, withInit, header]; simp
  have hn : F.judge [] (newExpr n) (.inst "Point" fields) [] caller .ivar0 :=
    @hF DClink.newInst (by simp [dclinks]) caller caller caller [] [] [] params
      .ivar0 .ivar0 .ivar0 fields .any fullClass init params _ _
      (hF DClink.constClass (by simp [dclinks]) hc)
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) rfl hc
      (by change init ∈ [getter, init]; simp) rfl (by decide)
      (by change "Point" ∈ ["Point"]; simp) rfl (by simp [params, FirstOrder, isAliasTy])
      rfl rfl (init_deriv rfl rfl rfl F hF) (by decide)
  have hr : F.judge [] (callExpr n) .int [] caller .ivar0 :=
    hF DClink.callSig (by simp [dclinks]) rfl
      (by simp [readerParams, FirstOrder, fields, isAliasTy]) rfl (reader_deriv F hF)
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) hn
        (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
      (by change reader ∈ [reader]; simp) rfl rfl rfl rfl rfl rfl rfl (by simp)
  exact hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks])
    (declaration_deriv F hF) (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hd
      (hF DClink.DJudgeSeq.last (by simp [dclinks]) hr)))

#print axioms full_deriv
end Ratchet.Denote.Typed.TopClassProgram

namespace Ratchet.Denote.Typed
open Ratchet.Denote
def program_075_class_instance_as_fun_arg : Ratchet.Expr := TopClassProgram.program 5
theorem safe_075_class_instance_as_fun_arg (hb : bootOkB = true) :
    StuckFree bootMachine program_075_class_instance_as_fun_arg :=
  dregistry_safe (TopClassProgram.full_deriv 5) (stateOk_boot hb)
#guard match RubyCore.Interp.run 400 (evalFrom bootMachine program_075_class_instance_as_fun_arg) with
  | .value (.int 5) _ => true
  | _ => false
#print axioms safe_075_class_instance_as_fun_arg
end Ratchet.Denote.Typed
