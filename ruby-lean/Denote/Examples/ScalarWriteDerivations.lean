import Denote.Clink.Registry

/-! Whole 074, with an independent derivation for every initial Integer. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ScalarWriteProgram
open RubyCore Ratchet Ratchet.Denote

def fields : Ty := .ivarCons "@size" .int .ivar0
def params : List SigParam := [("size", .int)]
def init : Defn := ⟨"initialize", [.req "size"], .vasgn .ivar "@size" (.var .lvar "size")⟩
def grow : Defn := ⟨"grow", [], .vasgn .ivar "@size" (.send (some (.var .ivar "@size")) "+" [.int 1] none)⟩
def header : Cls := classHeader "Box"
def entry : Ctx := classHeaderCtx (classBodyCtx ctx0 "Box") "Box"
def withInit : Cls := classWithMethod header init
def afterInit : Ctx := instanceDeclCtx entry header init
def fullClass : Cls := classWithMethod withInit grow
def afterGrow : Ctx := instanceDeclCtx afterInit withInit grow
def caller : Ctx := returnScopeCtx ctx0 afterGrow
def declaration : Ratchet.Expr := .class' "Box" none (.seq [
  .def' init.name init.params init.body, .def' grow.name grow.params grow.body])
def newExpr (n : Int) : Ratchet.Expr := .send (some (.const "Box")) "new" [.int n] none
def callExpr (n : Int) : Ratchet.Expr := .send (some (newExpr n)) "grow" [] none
def program (n : Int) : Ratchet.Expr := .seq [declaration, callExpr n]

private theorem init_deriv {κ : Ctx} (hs : κ.selfTy = some (.inst "Box" .ivar0))
    (hb : κ.blockTy = none) (hc : κ.consts = []) :
    (DJudgeC dclinks).init κ params .ivar0 init.body .any κ params fields := by
  intro F hF
  exact hF DClink.InitJudge.ignoreResult (by simp [dclinks])
    (hF DClink.InitJudge.ivarAsgn (by simp [dclinks])
      (hF DClink.InitJudge.var (by simp [dclinks]) rfl rfl) (by
        simp [writeTypesB, params, IvarStable, stripAlias, writeFieldsB, spineKeys, hs, hb, hc]))

private theorem grow_deriv {κ : Ctx} (hs : κ.selfTy = some (.inst "Box" fields))
    (hf : nameFreeN κ "+" = true) (ht : reframeTypesB κ fields = true) :
    (DJudgeC dclinks).judge [] grow.body .int [] κ fields := by
  intro F hF
  exact hF DClink.scalarIvarAsgn (by simp [dclinks])
    (hF DClink.prim (by simp [dclinks])
      (@hF DClink.ivarRead (by simp [dclinks]) κ [] fields "@size")
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
      DPrim.intAdd hf (by intro h; cases h)) hs rfl rfl ht rfl

private theorem declaration_deriv :
    (DJudgeC dclinks).judge [] declaration .sym [] ctx0 .ivar0 caller .ivar0 := by
  intro F hF
  have hi : F.judge [] (.def' init.name init.params init.body) .sym [] entry .ivar0 afterInit .ivar0 :=
    @hF DClink.initDef (by simp [dclinks]) entry [] params .ivar0 fields .any header init params
      rfl rfl (by simp [params, FirstOrder, isAliasTy]) rfl rfl (init_deriv rfl rfl rfl F hF)
      (by change header ∈ [header]; simp) (by decide)
  have hg : F.judge [] (.def' grow.name grow.params grow.body) .sym [] afterInit .ivar0 afterGrow .ivar0 :=
    @hF DClink.memberDef (by simp [dclinks]) afterInit [] [] .ivar0 fields .int withInit grow []
      rfl (by simp) rfl rfl (grow_deriv rfl (by decide) (by decide) F hF) (by decide)
      (by change withInit ∈ [withInit, header]; simp) (by decide)
  exact hF DClink.classDecl (by simp [dclinks])
    (hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hi
      (hF DClink.DJudgeSeq.last (by simp [dclinks]) hg))) (by decide)

theorem full_deriv (n : Int) :
    (DJudgeC dclinks).judge [] (program n) .int [] ctx0 .ivar0 caller .ivar0 := by
  intro F hF
  have hc : fullClass ∈ caller.classes := by change fullClass ∈ [fullClass, withInit, header]; simp
  have hn : F.judge [] (newExpr n) (.inst "Box" fields) [] caller .ivar0 :=
    @hF DClink.newInst (by simp [dclinks]) caller caller caller [] [] [] params
      .ivar0 .ivar0 .ivar0 fields .any fullClass init params _ _
      (hF DClink.constClass (by simp [dclinks]) hc)
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) rfl hc
      (by change init ∈ [grow, init]; simp) rfl (by decide)
      (by change "Box" ∈ ["Box"]; simp) rfl (by simp [params, FirstOrder, isAliasTy])
      rfl rfl (init_deriv rfl rfl rfl F hF) (by decide)
  have hg : F.judge [] (callExpr n) .int [] caller .ivar0 :=
    @hF DClink.callMethodSig (by simp [dclinks]) caller caller caller [] [] [] []
      .ivar0 .ivar0 .ivar0 fields .int fullClass grow [] _ _ hn
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl hc
      (by change grow ∈ [grow, init]; simp) (by decide) (by decide) rfl (by simp) rfl rfl
      (grow_deriv rfl (by decide) (by decide) F hF) (by decide)
  exact hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks])
    (declaration_deriv F hF) (hF DClink.DJudgeSeq.last (by simp [dclinks]) hg))

#print axioms full_deriv
end Ratchet.Denote.Typed.ScalarWriteProgram

namespace Ratchet.Denote.Typed
open Ratchet.Denote
def program_074_class_setter_method : Ratchet.Expr := ScalarWriteProgram.program 1
theorem safe_074_class_setter_method (hb : bootOkB = true) : StuckFree bootMachine program_074_class_setter_method :=
  dregistry_safe (ScalarWriteProgram.full_deriv 1) (stateOk_boot hb)
#guard match RubyCore.Interp.run 250 (evalFrom bootMachine program_074_class_setter_method) with
  | .value (.int 2) _ => true
  | _ => false
#print axioms safe_074_class_setter_method
end Ratchet.Denote.Typed
