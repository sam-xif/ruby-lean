import Denote.Typed.PointProgram
import Denote.Typed.Clink

/-! A constructor-wise worked 061 proof. Production rules quantify over every class/body;
this instance additionally lets RuleAudit inspect exactly the rules the program uses. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote PointClass

private theorem init_deriv {κ : Ctx} {cn : String}
    (hs : κ.selfTy = some (.inst cn .ivar0)) (hb : κ.blockTy = none) (hc : κ.consts = []) :
    (DJudgeC dclinks).init κ pointInitParams .ivar0 pointInitBody .any κ pointInitParams pointInitSpine := by
  intro F hF
  have hx : F.init κ pointInitParams .ivar0 (.vasgn .ivar "@x" (.var .lvar "x")) .int
      κ pointInitParams (.ivarCons "@x" .int .ivar0) :=
    hF DClink.InitJudge.ivarAsgn (by simp [dclinks])
      (hF DClink.InitJudge.var (by simp [dclinks]) rfl rfl) (by
        simp [writeTypesB, pointInitParams, IvarStable, stripAlias, writeFieldsB, spineKeys, hs, hb, hc])
  have hy : F.init κ pointInitParams (.ivarCons "@x" .int .ivar0)
      (.vasgn .ivar "@y" (.var .lvar "y")) .int κ pointInitParams pointInitSpine :=
    hF DClink.InitJudge.ivarAsgn (by simp [dclinks])
      (hF DClink.InitJudge.var (by simp [dclinks]) rfl rfl) (by
        simp [writeTypesB, pointInitParams, IvarStable, stripAlias, writeFieldsB, spineKeys, ivarGet?, hs, hb, hc])
  exact hF DClink.InitJudge.ignoreResult (by simp [dclinks])
    (hF DClink.InitJudge.seq (by simp [dclinks])
      (hF DClink.InitJudgeSeq.cons (by simp [dclinks]) hx
        (hF DClink.InitJudgeSeq.last (by simp [dclinks]) hy)))

private theorem class_deriv :
    (DJudgeC dclinks).judge [] program .sym [] ctx0 .ivar0 callerCtx .ivar0 := by
  intro F hF
  have hi : F.judge [] (.def' initDecl.name initDecl.params initDecl.body)
      .sym [] entryCtx .ivar0 afterInit .ivar0 :=
    @hF DClink.initDef (by simp [dclinks]) entryCtx [] pointInitParams .ivar0 pointInitSpine .any
      header initDecl pointInitParams rfl rfl
      (by simp [pointInitParams, FirstOrder, isAliasTy]) rfl (by decide)
      (init_deriv rfl rfl rfl F hF) (by change header ∈ [header]; simp) (by decide)
  have hg : F.judge [] (.def' getter.name getter.params getter.body)
      .sym [] afterInit .ivar0 bodyCtx .ivar0 :=
    @hF DClink.memberDef (by simp [dclinks]) afterInit [] [] .ivar0 pointInitSpine .int
      initClass getter [] rfl (by simp) rfl (by decide)
      (@hF DClink.ivarRead (by simp [dclinks])
        (instanceBodyCtx bodyCtx ⟨"Point", "Point", "getX"⟩ pointInitSpine) [] pointInitSpine "@x") (by decide)
      (by change initClass ∈ [initClass, header]; simp) (by decide)
  exact hF DClink.classDecl (by simp [dclinks])
    (hF DClink.seq (by simp [dclinks])
      (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hi
        (hF DClink.DJudgeSeq.last (by simp [dclinks]) hg))) (by decide)

private theorem new_deriv (x y : Int) :
    (DJudgeC dclinks).judge [] (newExpr x y) (.inst "Point" pointInitSpine) [] callerCtx .ivar0 := by
  intro F hF
  have hr : F.judge [] (.const "Point") (.clsOf "Point") [] callerCtx .ivar0 :=
    @hF DClink.constClass (by simp [dclinks]) callerCtx [] .ivar0 (classWithMethod initClass getter)
      (by change classWithMethod initClass getter ∈ [classWithMethod initClass getter, initClass, header]; simp)
  have ha : F.all [] [.int x, .int y] [.int, .int] [] callerCtx .ivar0 :=
    hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) rfl
  exact @hF DClink.newInst (by simp [dclinks]) callerCtx callerCtx callerCtx
    [] [] [] pointInitParams .ivar0 .ivar0 .ivar0 pointInitSpine .any
    (classWithMethod initClass getter) initDecl pointInitParams _ _ hr ha rfl
    (by change classWithMethod initClass getter ∈ [classWithMethod initClass getter, initClass, header]; simp)
    (by change initDecl ∈ [getter, initDecl]; simp) rfl (by decide)
    (by change "Point" ∈ ["Point"]; simp) rfl (by simp [pointInitParams, FirstOrder, isAliasTy])
    rfl (by decide) (init_deriv rfl rfl rfl F hF) (by decide)

def program_061_class_basic : Ratchet.Expr := fullProgram 1 2

theorem derivD_class_basic (x y : Int) :
    (DJudgeC dclinks).judge [] (fullProgram x y) .int [] ctx0 .ivar0 callerCtx .ivar0 := by
  intro F hF
  have hg : F.judge [] (getExpr x y) .int [] callerCtx .ivar0 :=
    @hF DClink.callMethodSig (by simp [dclinks]) callerCtx callerCtx callerCtx
      [] [] [] [] .ivar0 .ivar0 .ivar0 pointInitSpine .int
      (classWithMethod initClass getter) getter [] _ _ (new_deriv x y F hF)
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl
      (by change classWithMethod initClass getter ∈ [classWithMethod initClass getter, initClass, header]; simp)
      (by change getter ∈ [getter, initDecl]; simp) (by decide) (by decide)
      rfl (by simp) rfl (by decide)
      (@hF DClink.ivarRead (by simp [dclinks])
        (instanceBodyCtx callerCtx ⟨"Point", "Point", "getX"⟩ pointInitSpine) [] pointInitSpine "@x") (by decide)
  exact hF DClink.seq (by simp [dclinks])
    (hF DClink.DJudgeSeq.cons (by simp [dclinks]) (class_deriv F hF)
      (hF DClink.DJudgeSeq.last (by simp [dclinks]) hg))

theorem safe_061_class_basic (hb : bootOkB = true) : StuckFree bootMachine program_061_class_basic :=
  dregistry_safe (derivD_class_basic 1 2) (stateOk_boot hb)

#print axioms derivD_class_basic
#print axioms safe_061_class_basic
end Ratchet.Denote.Typed
