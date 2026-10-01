import Denote.Examples.ClassDerivations
import Denote.Controls.FactoryConstructorControls

/-! Independent rule-by-rule derivation of whole 073. No evaluation of validateD supplies
this proof; the rule audit separately checks its exact rule set. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.FactoryDerivations
open RubyCore Ratchet Ratchet.Denote FactoryConstructorControls
open PointClass (entryCtx initDecl afterInit initClass header)

private theorem point_mem : point ∈ callerCtx.classes := by
  change point ∈ [point, initClass, header]; simp

private theorem body_deriv :
    (DJudgeC dclinks).judge [] factory.body (.cls "Point") [] factoryCtx .ivar0 := by
  intro F hF
  have ha : F.all [] [.int 0, .int 0] [.int, .int] [] factoryCtx .ivar0 :=
    hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) rfl
  have hn : F.judge [] factory.body (.inst "Point" pointInitSpine) [] factoryCtx .ivar0 :=
    @hF DClink.newImplicit (by simp [dclinks]) factoryCtx factoryCtx [] [] pointInitParams
      .ivar0 .ivar0 pointInitSpine .any point initDecl pointInitParams _ rfl ha point_mem
      (by change initDecl ∈ [initDecl]; simp) rfl (by decide)
      (by change "Point" ∈ ["Point"]; simp) rfl
      (by simp [pointInitParams, FirstOrder, isAliasTy]) rfl (by decide)
      (point_init_deriv rfl rfl rfl F hF) (by decide)
  exact @hF DClink.instanceType (by simp [dclinks]) factoryCtx factoryCtx [] []
    .ivar0 .ivar0 pointInitSpine point factory.body hn point_mem

private theorem declaration_deriv :
    (DJudgeC dclinks).judge [] declaration .sym [] ctx0 .ivar0 callerCtx .ivar0 := by
  intro F hF
  have hi : F.judge [] (.def' initDecl.name initDecl.params initDecl.body)
      .sym [] entryCtx .ivar0 afterInit .ivar0 :=
    @hF DClink.initDef (by simp [dclinks]) entryCtx [] pointInitParams .ivar0 pointInitSpine .any
      header initDecl pointInitParams rfl rfl (by simp [pointInitParams, FirstOrder, isAliasTy])
      rfl (by decide) (point_init_deriv rfl rfl rfl F hF)
      (by change header ∈ [header]; simp) (by decide)
  have hs : F.judge [] (.defs .self' factory.name factory.params factory.body)
      .sym [] afterInit .ivar0 afterFactory .ivar0 :=
    @hF DClink.singletonDef (by simp [dclinks]) afterInit [] [] .ivar0 (.cls "Point")
      initClass factory [] rfl (by simp) rfl (body_deriv F hF)
      (by change initClass ∈ [initClass, header]; simp) (by decide)
  exact hF DClink.classDecl (by simp [dclinks])
    (hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hi
      (hF DClink.DJudgeSeq.last (by simp [dclinks]) hs))) (by decide)

theorem full_deriv :
    (DJudgeC dclinks).judge [] program (.cls "Point") [] ctx0 .ivar0 callerCtx .ivar0 := by
  intro F hF
  have hc : F.judge [] call (.cls "Point") [] callerCtx .ivar0 :=
    @hF DClink.callSingleton (by simp [dclinks]) callerCtx callerCtx callerCtx [] [] [] []
      .ivar0 .ivar0 .ivar0 (.cls "Point") point factory [] _ _
      (hF DClink.constClass (by simp [dclinks]) point_mem)
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) point_mem
      (by change factory ∈ [factory]; simp) (by decide) rfl (by simp) rfl (body_deriv F hF) (by decide)
  exact hF DClink.seq (by simp [dclinks])
    (hF DClink.DJudgeSeq.cons (by simp [dclinks]) (declaration_deriv F hF)
      (hF DClink.DJudgeSeq.last (by simp [dclinks]) hc))

#print axioms full_deriv
end Ratchet.Denote.Typed.FactoryDerivations

namespace Ratchet.Denote.Typed
open Ratchet.Denote
def program_073_class_factory_method : Ratchet.Expr := FactoryConstructorControls.program
theorem safe_073_class_factory_method (hb : bootOkB = true) : StuckFree bootMachine program_073_class_factory_method :=
  dregistry_safe FactoryDerivations.full_deriv (stateOk_boot hb)
#print axioms safe_073_class_factory_method
end Ratchet.Denote.Typed
