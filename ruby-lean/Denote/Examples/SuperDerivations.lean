import Denote.Clink.Registry

/-! Independently audited whole 067, parameterized by the Integer passed to super. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace Ratchet.Denote.Typed.SuperProgram
open RubyCore Ratchet Ratchet.Denote

def params : List SigParam := [("sides", .int)]
def fields : Ty := .ivarCons "@sides" .int .ivar0
def init : Defn := ⟨"initialize", [.req "sides"], .vasgn .ivar "@sides" (.var .lvar "sides")⟩
def speak : Defn := ⟨"sides", [], .var .ivar "@sides"⟩
def header : Cls := classHeader "Shape"
def entryCtx : Ctx := classHeaderCtx (classBodyCtx ctx0 "Shape") "Shape"
def afterInit : Ctx := instanceDeclCtx entryCtx header init
def initClass : Cls := classWithMethod header init
def bodyCtx : Ctx := instanceDeclCtx afterInit initClass speak
def parent : Cls := classWithMethod initClass speak
def parentCtx : Ctx := returnScopeCtx ctx0 bodyCtx
def childInit (n : Int) : Defn := ⟨"initialize", [], .super' [.int n] none⟩
def childHeader : Cls := subclassHeader "Triangle" "Shape"
def childEntry : Ctx := subclassHeaderCtx (classBodyCtx parentCtx "Triangle") "Triangle" "Shape"
def childBody (n : Int) : Ctx := instanceDeclCtx childEntry childHeader (childInit n)
def child (n : Int) : Cls := classWithMethod childHeader (childInit n)
def callerCtx (n : Int) : Ctx := returnScopeCtx parentCtx (childBody n)
def parentExpr : Ratchet.Expr := .class' "Shape" none (.seq [
  .def' init.name init.params init.body, .def' speak.name speak.params speak.body])
def childExpr (n : Int) : Ratchet.Expr := .class' "Triangle" (some (.const "Shape"))
  (.def' "initialize" [] (childInit n).body)
def newExpr : Ratchet.Expr := .send (some (.const "Triangle")) "new" [] none
def getExpr : Ratchet.Expr := .send (some newExpr) "sides" [] none
def program (n : Int) : Ratchet.Expr := .seq [parentExpr, childExpr n, getExpr]

private theorem init_deriv {κ : Ctx} {cn : String}
    (hs : κ.selfTy = some (.inst cn .ivar0)) (hb : κ.blockTy = none) (hc : κ.consts = []) :
    (DJudgeC dclinks).init κ params .ivar0 init.body .any κ params fields := by
  intro F hF
  exact hF DClink.InitJudge.ignoreResult (by simp [dclinks])
    (hF DClink.InitJudge.ivarAsgn (by simp [dclinks])
      (hF DClink.InitJudge.var (by simp [dclinks]) rfl rfl) (by
        simp [writeTypesB, params, IvarStable, stripAlias, writeFieldsB, spineKeys, hs, hb, hc]))

private theorem parent_deriv :
    (DJudgeC dclinks).judge [] parentExpr .sym [] ctx0 .ivar0 parentCtx .ivar0 := by
  intro F hF
  have hi : F.judge [] (.def' init.name init.params init.body) .sym [] entryCtx .ivar0 afterInit .ivar0 :=
    @hF DClink.initDef (by simp [dclinks]) entryCtx [] params .ivar0 fields .any header init params
      rfl rfl (by simp [params, FirstOrder, isAliasTy]) rfl rfl
      (init_deriv rfl rfl rfl F hF) (by change header ∈ [header]; simp) (by decide)
  have hs : F.judge [] (.def' speak.name speak.params speak.body) .sym [] afterInit .ivar0 bodyCtx .ivar0 :=
    @hF DClink.memberDef (by simp [dclinks]) afterInit [] [] .ivar0 fields .int
      initClass speak [] rfl (by simp) rfl rfl
      (@hF DClink.ivarRead (by simp [dclinks])
        (instanceBodyCtx bodyCtx ⟨"Shape", "Shape", "sides"⟩ fields) [] fields "@sides") (by decide)
      (by change initClass ∈ [initClass, header]; simp) (by decide)
  exact hF DClink.classDecl (by simp [dclinks])
    (hF DClink.seq (by simp [dclinks])
      (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hi
        (hF DClink.DJudgeSeq.last (by simp [dclinks]) hs))) (by decide)

private theorem child_init_deriv {κ : Ctx} (n : Int)
    (hc : child n ∈ κ.classes)
    (route : SuperRoute κ.classes "Triangle" "Triangle" "Shape" init)
    (hg : superInitB κ [] .ivar0 fields (child n) "Triangle" init params .any = true)
    (hconst : κ.consts = []) :
    (DJudgeC dclinks).init κ [] .ivar0 (childInit n).body .any κ [] fields := by
  intro F hF
  exact @hF DClink.InitJudge.superInit (by simp [dclinks]) κ [] [] params
    .ivar0 .ivar0 fields .any [.int n] (child n) "Triangle" "Shape" init params
    (hF DClink.InitJudgeAll.cons (by simp [dclinks])
      (hF DClink.InitJudge.intLit (by simp [dclinks]))
      (hF DClink.InitJudgeAll.nil (by simp [dclinks])) rfl rfl)
    (init_deriv (κ := initializerBodyCtxAt κ "Triangle" "Shape") rfl rfl hconst F hF) hc route hg

private theorem child_deriv (n : Int) :
    (DJudgeC dclinks).judge [] (childExpr n) .sym [] parentCtx .ivar0 (callerCtx n) .ivar0 := by
  intro F hF
  apply @hF DClink.subclassDecl (by simp [dclinks]) parentCtx parentCtx (childBody n)
    [] [] [] .ivar0 .ivar0 .ivar0 .sym parent "Triangle" (.const "Shape")
    (.def' "initialize" [] (childInit n).body)
  · exact @hF DClink.constClass (by simp [dclinks]) parentCtx [] .ivar0 parent
      (by change parent ∈ [parent, initClass, header]; simp)
  · change parent ∈ [parent, initClass, header]; simp
  · exact @hF DClink.initDef (by simp [dclinks]) childEntry [] [] .ivar0 fields .any
      childHeader (childInit n) [] rfl rfl (by simp) rfl rfl
      (child_init_deriv (κ := initializerBodyCtx (childBody n) "Triangle") n
        (by change child n ∈ [child n, childHeader, parent, initClass, header]; simp)
        ((superRoute? (childBody n).classes "Triangle" "Triangle" "Shape" init).get (by exact of_decide_eq_true rfl))
        (by exact of_decide_eq_true rfl) rfl F hF)
      (by change childHeader ∈ [childHeader, parent, initClass, header]; simp) (by exact of_decide_eq_true rfl)
  · rfl

private theorem new_deriv (n : Int) :
    (DJudgeC dclinks).judge [] newExpr (.inst "Triangle" fields) [] (callerCtx n) .ivar0 := by
  intro F hF
  have hc : child n ∈ (callerCtx n).classes := by
    change child n ∈ [child n, childHeader, parent, initClass, header]; simp
  exact @hF DClink.newInst (by simp [dclinks]) (callerCtx n) (callerCtx n) (callerCtx n)
    [] [] [] [] .ivar0 .ivar0 .ivar0 fields .any (child n) (childInit n) [] _ _
    (@hF DClink.constClass (by simp [dclinks]) (callerCtx n) [] .ivar0 (child n) hc)
    (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl hc
    (by change childInit n ∈ [childInit n]; simp) rfl (by exact of_decide_eq_true rfl)
    (by change "Triangle" ∈ ["Triangle", "Shape"]; simp) rfl (by simp) rfl
    (by exact of_decide_eq_true rfl)
    (child_init_deriv (κ := initializerBodyCtx (callerCtx n) "Triangle") n hc
      ((superRoute? (callerCtx n).classes "Triangle" "Triangle" "Shape" init).get (by exact of_decide_eq_true rfl))
      (by exact of_decide_eq_true rfl) rfl F hF) (by exact of_decide_eq_true rfl)

theorem full_deriv (n : Int) :
    (DJudgeC dclinks).judge [] (program n) .int [] ctx0 .ivar0 (callerCtx n) .ivar0 := by
  intro F hF
  have hg : F.judge [] getExpr .int [] (callerCtx n) .ivar0 :=
    @hF DClink.callInherited (by simp [dclinks]) (callerCtx n) (callerCtx n) (callerCtx n)
      [] [] [] [] .ivar0 .ivar0 .ivar0 fields .int (child n) "Shape" speak [] _ _
      (new_deriv n F hF) (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl
      (by change child n ∈ [child n, childHeader, parent, initClass, header]; simp)
      ((memberRoute? (callerCtx n).classes "Triangle" "Shape" speak).get (by exact of_decide_eq_true rfl))
      (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl)
      rfl (by simp) rfl rfl
      (@hF DClink.ivarRead (by simp [dclinks])
        (instanceBodyCtx (callerCtx n) ⟨"Triangle", "Shape", "sides"⟩ fields) [] fields "@sides")
      (by exact of_decide_eq_true rfl)
  exact hF DClink.seq (by simp [dclinks])
    (hF DClink.DJudgeSeq.cons (by simp [dclinks]) (parent_deriv F hF)
      (hF DClink.DJudgeSeq.cons (by simp [dclinks]) (child_deriv n F hF)
        (hF DClink.DJudgeSeq.last (by simp [dclinks]) hg)))

#print axioms full_deriv
end Ratchet.Denote.Typed.SuperProgram

namespace Ratchet.Denote.Typed
open Ratchet.Denote
def program_067_class_super_call : Ratchet.Expr := SuperProgram.program 3
theorem safe_067_class_super_call (hb : bootOkB = true) : StuckFree bootMachine program_067_class_super_call :=
  dregistry_safe (SuperProgram.full_deriv 3) (stateOk_boot hb)
#print axioms safe_067_class_super_call
#guard match RubyCore.Interp.run 240 (evalFrom bootMachine program_067_class_super_call) with
  | .value (.int 3) _ => true
  | _ => false
end Ratchet.Denote.Typed
