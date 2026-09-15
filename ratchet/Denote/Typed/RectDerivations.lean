import Denote.Typed.Clink

/-! Worked 064 proof for the independent proof-term audit. All production call/return
lemmas are class-generic; Rect is only the corpus instance, checked at annotation domains. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.Rect
open RubyCore Ratchet Ratchet.Denote

def params : Env := [("w", .int), ("h", .int)]
def fields : Ty := .ivarCons "@w" .int (.ivarCons "@h" .int .ivar0)
def init : Defn := ⟨"initialize", [.req "w", .req "h"], .seq [
  .vasgn .ivar "@w" (.var .lvar "w"), .vasgn .ivar "@h" (.var .lvar "h")]⟩
def area : Defn := ⟨"area", [], .send (some (.var .ivar "@w")) "*" [.var .ivar "@h"] none⟩
def describe : Defn := ⟨"describe", [], .send (some (.str "area=")) "+"
  [.send (some (.vcall "area")) "to_s" [] none] none⟩
def header : Cls := classHeader "Rect"
def entryCtx : Ctx := classHeaderCtx (classBodyCtx ctx0 "Rect") "Rect"
def initClass : Cls := classWithMethod header init
def afterInit : Ctx := instanceDeclCtx entryCtx header init
def areaClass : Cls := classWithMethod initClass area
def afterArea : Ctx := instanceDeclCtx afterInit initClass area
def fullClass : Cls := classWithMethod areaClass describe
def bodyCtx : Ctx := instanceDeclCtx afterArea areaClass describe
def callerCtx : Ctx := returnScopeCtx ctx0 bodyCtx
def classExpr : Ratchet.Expr := .class' "Rect" none (.seq [
  .def' init.name init.params init.body, .def' area.name area.params area.body,
  .def' describe.name describe.params describe.body])
def newExpr : Ratchet.Expr := .send (some (.const "Rect")) "new" [.int 3, .int 4] none
def getExpr : Ratchet.Expr := .send (some newExpr) "describe" [] none

private theorem init_deriv {κ : Ctx}
    (hs : κ.selfTy = some (.inst "Rect" .ivar0)) (hb : κ.blockTy = none) (hc : κ.consts = []) :
    (DJudgeC dclinks).init κ params .ivar0 init.body .any κ params fields := by
  intro F hF
  have hw : F.init κ params .ivar0 (.vasgn .ivar "@w" (.var .lvar "w")) .int
      κ params (.ivarCons "@w" .int .ivar0) :=
    hF DClink.InitJudge.ivarAsgn (by simp [dclinks])
      (hF DClink.InitJudge.var (by simp [dclinks]) rfl rfl) (by
        simp [writeTypesB, params, IvarStable, stripAlias, writeFieldsB, spineKeys, hs, hb, hc])
  have hh : F.init κ params (.ivarCons "@w" .int .ivar0)
      (.vasgn .ivar "@h" (.var .lvar "h")) .int κ params fields :=
    @hF DClink.InitJudge.ivarAsgn (by simp [dclinks]) κ κ params params
      (.ivarCons "@w" .int .ivar0) (.ivarCons "@w" .int .ivar0) .int "@h" (.var .lvar "h")
      (hF DClink.InitJudge.var (by simp [dclinks]) rfl rfl) (by
        simp [writeTypesB, params, IvarStable, stripAlias, writeFieldsB, spineKeys, ivarGet?, hs, hb, hc])
  exact hF DClink.InitJudge.ignoreResult (by simp [dclinks])
    (hF DClink.InitJudge.seq (by simp [dclinks])
      (hF DClink.InitJudgeSeq.cons (by simp [dclinks]) hw
        (hF DClink.InitJudgeSeq.last (by simp [dclinks]) hh)))

private theorem area_deriv {κ : Ctx} (hf : nameFreeN κ "*" = true) :
    (DJudgeC dclinks).judge [] area.body .int [] κ fields := by
  intro F hF
  exact hF DClink.prim (by simp [dclinks])
    (@hF DClink.ivarRead (by simp [dclinks]) κ [] fields "@w")
    (hF DClink.DJudgeAll.cons (by simp [dclinks])
      (@hF DClink.ivarRead (by simp [dclinks]) κ [] fields "@h")
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) DPrim.intMul hf (by intro h; cases h)

private theorem describe_deriv {κ : Ctx} (hs : κ.selfTy = some (.inst "Rect" fields))
    (hc : fullClass ∈ κ.classes) (hg : instanceCallB κ [] fields = true)
    (hf : ∀ name ∈ ["*", "to_s", "+"], nameFreeN κ name = true)
    (hno : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    (DJudgeC dclinks).judge [] describe.body (.cls "String") [] κ fields := by
  intro F hF
  have hv : F.judge [] (.vcall "area") .int [] κ fields :=
    @hF DClink.vcallMethodSig (by simp [dclinks]) κ [] [] fields fields .int fullClass area hs hc
      (by change area ∈ [describe, area, init]; simp) (by decide) (by decide) rfl rfl rfl
      (area_deriv (κ := instanceBodyCtx κ ⟨"Rect", "Rect", "area"⟩ fields)
        (hf "*" (by simp)) F hF) hg
  have ht : F.judge [] (.send (some (.vcall "area")) "to_s" [] none) (.cls "String") [] κ fields :=
    hF DClink.prim (by simp [dclinks]) hv (hF DClink.DJudgeAll.nil (by simp [dclinks]))
      DPrim.intToS (hf "to_s" (by simp)) (by intro h; cases h)
  exact hF DClink.prim (by simp [dclinks]) (hF DClink.strLit (by simp [dclinks]))
    (hF DClink.DJudgeAll.cons (by simp [dclinks]) ht (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
    DPrim.strAdd (hf "+" (by simp)) (fun _ => hno)

private theorem class_deriv :
    (DJudgeC dclinks).judge [] classExpr .sym [] ctx0 .ivar0 callerCtx .ivar0 := by
  intro F hF
  have hi : F.judge [] (.def' init.name init.params init.body) .sym [] entryCtx .ivar0 afterInit .ivar0 :=
    @hF DClink.initDef (by simp [dclinks]) entryCtx [] params .ivar0 fields .any header init params
      rfl rfl (by simp [params, FirstOrder, isAliasTy]) rfl rfl (init_deriv rfl rfl rfl F hF)
      (by change header ∈ [header]; simp) (by decide)
  have ha : F.judge [] (.def' area.name area.params area.body) .sym [] afterInit .ivar0 afterArea .ivar0 :=
    @hF DClink.memberDef (by simp [dclinks]) afterInit [] [] .ivar0 fields .int initClass area []
      rfl (by simp) rfl rfl (area_deriv (by decide) F hF) (by decide)
      (by change initClass ∈ [initClass, header]; simp) (by decide)
  have hd : F.judge [] (.def' describe.name describe.params describe.body) .sym []
      afterArea .ivar0 bodyCtx .ivar0 :=
    @hF DClink.memberDef (by simp [dclinks]) afterArea [] [] .ivar0 fields (.cls "String")
      areaClass describe [] rfl (by simp) rfl rfl
      (describe_deriv rfl (by change fullClass ∈ [fullClass, areaClass, initClass, header]; simp)
        (by decide) (by intro name hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                        rcases hn with rfl | rfl | rfl <;> decide) (by decide) F hF)
      (by decide) (by change areaClass ∈ [areaClass, initClass, header]; simp) (by decide)
  exact hF DClink.classDecl (by simp [dclinks])
    (hF DClink.seq (by simp [dclinks])
      (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hi
        (hF DClink.DJudgeSeq.cons (by simp [dclinks]) ha
          (hF DClink.DJudgeSeq.last (by simp [dclinks]) hd)))) (by decide)

private theorem new_deriv : (DJudgeC dclinks).judge [] newExpr (.inst "Rect" fields) [] callerCtx .ivar0 := by
  intro F hF
  have hr : F.judge [] (.const "Rect") (.clsOf "Rect") [] callerCtx .ivar0 :=
    @hF DClink.constClass (by simp [dclinks]) callerCtx [] .ivar0 fullClass
      (by change fullClass ∈ [fullClass, areaClass, initClass, header]; simp)
  have ha : F.all [] [.int 3, .int 4] [.int, .int] [] callerCtx .ivar0 :=
    hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) rfl
  exact @hF DClink.newInst (by simp [dclinks]) callerCtx callerCtx callerCtx [] [] [] params
    .ivar0 .ivar0 .ivar0 fields .any fullClass init params _ _ hr ha rfl
    (by change fullClass ∈ [fullClass, areaClass, initClass, header]; simp)
    (by change init ∈ [describe, area, init]; simp) rfl (by decide)
    (by change "Rect" ∈ ["Rect"]; simp) rfl (by simp [params, FirstOrder, isAliasTy])
    rfl rfl (init_deriv rfl rfl rfl F hF) (by decide)

theorem full_deriv : (DJudgeC dclinks).judge [] (.seq [classExpr, getExpr]) (.cls "String") []
    ctx0 .ivar0 callerCtx .ivar0 := by
  intro F hF
  have hg : F.judge [] getExpr (.cls "String") [] callerCtx .ivar0 :=
    @hF DClink.callMethodSig (by simp [dclinks]) callerCtx callerCtx callerCtx [] [] [] []
      .ivar0 .ivar0 .ivar0 fields (.cls "String") fullClass describe [] _ _ (new_deriv F hF)
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl
      (by change fullClass ∈ [fullClass, areaClass, initClass, header]; simp)
      (by change describe ∈ [describe, area, init]; simp) (by decide) (by decide) rfl (by simp) rfl rfl
      (describe_deriv rfl (by change fullClass ∈ [fullClass, areaClass, initClass, header]; simp)
        (by decide) (by intro name hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                        rcases hn with rfl | rfl | rfl <;> decide) (by decide) F hF) (by decide)
  exact hF DClink.seq (by simp [dclinks])
    (hF DClink.DJudgeSeq.cons (by simp [dclinks]) (class_deriv F hF)
      (hF DClink.DJudgeSeq.last (by simp [dclinks]) hg))

#print axioms full_deriv
end Ratchet.Denote.Typed.Rect

namespace Ratchet.Denote.Typed
open Ratchet.Denote
def program_064_class_method_calls_method : Ratchet.Expr := .seq [Rect.classExpr, Rect.getExpr]
theorem safe_064_class_method_calls_method (hb : bootOkB = true) :
    StuckFree bootMachine program_064_class_method_calls_method :=
  dregistry_safe Rect.full_deriv (stateOk_boot hb)
#print axioms safe_064_class_method_calls_method
#guard match RubyCore.Interp.run 300 (evalFrom bootMachine program_064_class_method_calls_method) with
  | .value (.ref o) n => match (n.heap.get o).payload with
    | .str s => s == "area=12"
    | _ => false
  | _ => false
end Ratchet.Denote.Typed
