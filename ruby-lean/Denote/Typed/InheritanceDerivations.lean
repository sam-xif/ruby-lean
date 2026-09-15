import Denote.Typed.Clink

/-! Independently audited whole 065 derivation. All production inheritance rules are
class/owner/body/type-generic; Animal and Dog instantiate them here. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.Inheritance
open RubyCore Ratchet Ratchet.Denote

def params : List SigParam := [("name", .cls "String")]
def fields : Ty := .ivarCons "@name" (.cls "String") .ivar0
def init : Defn := ⟨"initialize", [.req "name"], .vasgn .ivar "@name" (.var .lvar "name")⟩
def speak : Defn := ⟨"speak", [], .var .ivar "@name"⟩
def header : Cls := classHeader "Animal"
def entryCtx : Ctx := classHeaderCtx (classBodyCtx ctx0 "Animal") "Animal"
def afterInit : Ctx := instanceDeclCtx entryCtx header init
def initClass : Cls := classWithMethod header init
def bodyCtx : Ctx := instanceDeclCtx afterInit initClass speak
def parent : Cls := classWithMethod initClass speak
def parentCtx : Ctx := returnScopeCtx ctx0 bodyCtx
def child : Cls := subclassHeader "Dog" "Animal"
def childCtx : Ctx := subclassHeaderCtx (classBodyCtx parentCtx "Dog") "Dog" "Animal"
def callerCtx : Ctx := returnScopeCtx parentCtx childCtx
def parentExpr : Ratchet.Expr := .class' "Animal" none (.seq [
  .def' init.name init.params init.body, .def' speak.name speak.params speak.body])
def childExpr : Ratchet.Expr := .class' "Dog" (some (.const "Animal")) .nil
def newExpr (s : String) : Ratchet.Expr := .send (some (.const "Dog")) "new" [.str s] none
def getExpr (s : String) : Ratchet.Expr := .send (some (newExpr s)) "speak" [] none
def program (s : String) : Ratchet.Expr := .seq [parentExpr, childExpr, getExpr s]

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
    @hF DClink.memberDef (by simp [dclinks]) afterInit [] [] .ivar0 fields (.cls "String")
      initClass speak [] rfl (by simp) rfl rfl
      (@hF DClink.ivarRead (by simp [dclinks])
        (instanceBodyCtx bodyCtx ⟨"Animal", "Animal", "speak"⟩ fields) [] fields "@name") (by decide)
      (by change initClass ∈ [initClass, header]; simp) (by decide)
  exact hF DClink.classDecl (by simp [dclinks])
    (hF DClink.seq (by simp [dclinks])
      (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hi
        (hF DClink.DJudgeSeq.last (by simp [dclinks]) hs))) (by decide)

private theorem child_deriv :
    (DJudgeC dclinks).judge [] childExpr .nilT [] parentCtx .ivar0 callerCtx .ivar0 := by
  intro F hF
  exact @hF DClink.subclassDecl (by simp [dclinks]) parentCtx parentCtx childCtx
    [] [] [] .ivar0 .ivar0 .ivar0 .nilT parent "Dog" (.const "Animal") .nil
    (@hF DClink.constClass (by simp [dclinks]) parentCtx [] .ivar0 parent
      (by change parent ∈ [parent, initClass, header]; simp))
    (by change parent ∈ [parent, initClass, header]; simp)
    (hF DClink.nilLit (by simp [dclinks])) (by decide)

private def initRoute : MemberRoute callerCtx.classes "Dog" "Animal" init :=
  (memberRoute? callerCtx.classes "Dog" "Animal" init).get (by decide)
private def speakRoute : MemberRoute callerCtx.classes "Dog" "Animal" speak :=
  (memberRoute? callerCtx.classes "Dog" "Animal" speak).get (by decide)

private theorem new_deriv (s : String) :
    (DJudgeC dclinks).judge [] (newExpr s) (.inst "Dog" fields) [] callerCtx .ivar0 := by
  intro F hF
  have hr : F.judge [] (.const "Dog") (.clsOf "Dog") [] callerCtx .ivar0 :=
    @hF DClink.constClass (by simp [dclinks]) callerCtx [] .ivar0 child
      (by change child ∈ [child, parent, initClass, header]; simp)
  have ha : F.all [] [.str s] [.cls "String"] [] callerCtx .ivar0 :=
    hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.strLit (by simp [dclinks]))
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl
  exact @hF DClink.newInherited (by simp [dclinks]) callerCtx callerCtx callerCtx
    [] [] [] params .ivar0 .ivar0 .ivar0 fields .any child "Animal" init params _ _ hr ha rfl
    (by change child ∈ [child, parent, initClass, header]; simp) initRoute rfl (by decide)
    (by change "Dog" ∈ ["Dog", "Animal"]; simp) rfl (by simp [params, FirstOrder, isAliasTy])
    rfl rfl (init_deriv rfl rfl rfl F hF) (by decide)

theorem full_deriv (s : String) :
    (DJudgeC dclinks).judge [] (program s) (.cls "String") [] ctx0 .ivar0 callerCtx .ivar0 := by
  intro F hF
  have hg : F.judge [] (getExpr s) (.cls "String") [] callerCtx .ivar0 :=
    @hF DClink.callInherited (by simp [dclinks]) callerCtx callerCtx callerCtx
      [] [] [] [] .ivar0 .ivar0 .ivar0 fields (.cls "String") child "Animal" speak [] _ _
      (new_deriv s F hF) (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl
      (by change child ∈ [child, parent, initClass, header]; simp) speakRoute
      (by decide) (by decide) (by decide +kernel) rfl (by simp) rfl rfl
      (@hF DClink.ivarRead (by simp [dclinks])
        (instanceBodyCtx callerCtx ⟨"Dog", "Animal", "speak"⟩ fields) [] fields "@name") (by decide)
  exact hF DClink.seq (by simp [dclinks])
    (hF DClink.DJudgeSeq.cons (by simp [dclinks]) (parent_deriv F hF)
      (hF DClink.DJudgeSeq.cons (by simp [dclinks]) (child_deriv F hF)
        (hF DClink.DJudgeSeq.last (by simp [dclinks]) hg)))

#print axioms full_deriv
end Ratchet.Denote.Typed.Inheritance

namespace Ratchet.Denote.Typed
open Ratchet.Denote
def program_065_class_inheritance_field : Ratchet.Expr := Inheritance.program "Rex"
theorem safe_065_class_inheritance_field (hb : bootOkB = true) :
    StuckFree bootMachine program_065_class_inheritance_field :=
  dregistry_safe (Inheritance.full_deriv "Rex") (stateOk_boot hb)
#print axioms safe_065_class_inheritance_field
#guard match RubyCore.Interp.run 300 (evalFrom bootMachine program_065_class_inheritance_field) with
  | .value (.ref o) n => match (n.heap.get o).payload with
    | .str s => s == "Rex"
    | _ => false
  | _ => false
end Ratchet.Denote.Typed
