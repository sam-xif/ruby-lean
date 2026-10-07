import Books.TypeSoundness.Examples.PointClass
import Books.TypeSoundness.Rules.Constructor.ConstructorImplicit
import Books.TypeSoundness.Rules.Singleton.SingletonDefine
import Books.TypeSoundness.Rules.Singleton.SingletonExpr

/-! The complete 073 factory, semantically: annotated initializer, def-self, implicit new,
singleton return, and final class-valued send. Validator admission is still separate. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.FactoryConstructorControls
open RubyCore Checker Checker.Soundness
open PointClass (entryCtx initDecl afterInit initClass header)

def factory : Defn := ⟨"origin", [], .send none "new" [.int 0, .int 0] none⟩
def point : Cls := classWithSingleton initClass factory
def afterFactory : Ctx := singletonDeclCtx afterInit initClass factory
def callerCtx : Ctx := returnScopeCtx ctx0 afterFactory
def factoryCtx : Ctx := singletonBodyCtx callerCtx "Point" "origin"
def classBody : Checker.Expr := .seq [.def' initDecl.name initDecl.params initDecl.body,
  .defs .self' factory.name factory.params factory.body]
def declaration : Checker.Expr := .class' "Point" none classBody
def call : Checker.Expr := .send (some (.const "Point")) "origin" [] none
def program : Checker.Expr := .seq [declaration, call]

private theorem point_mem : point ∈ callerCtx.classes := by
  change point ∈ [point, initClass, header]; simp

private theorem initializer_sem :
    SemInitA (initializerBodyCtx factoryCtx "Point") pointInitParams .ivar0 pointInitBody .any
      (initializerBodyCtx factoryCtx "Point") pointInitParams pointInitSpine :=
  point_initializer_sem rfl rfl rfl

/-- The constructor proof covers the full Integer domain and restores singleton scope. -/
theorem factory_body (x y : Int) :
    SemSafeCtxA factoryCtx [] .ivar0 (.send none "new" [.int x, .int y] none)
      (.inst "Point" pointInitSpine) factoryCtx [] .ivar0 := by
  exact SemSafeCtxA.constructImplicit (c := point) (d := initDecl) (ps := pointInitParams) rfl
    (.cons .intLit (.cons .intLit .nil rfl) rfl) point_mem
    (by change initDecl ∈ [initDecl]; simp) rfl (by decide) (by change "Point" ∈ ["Point"]; simp)
    rfl (by simp [pointInitParams, FirstOrder, isAliasTy]) initializer_sem
    (reframeTypesB_sound (by decide)) rfl (callWorldB_sound (by decide))
    (fun name => (constGet?_empty (κ := initializerBodyCtx factoryCtx "Point") rfl name).trans
      (constGet?_empty rfl name).symm) (by simp) (by decide)

theorem explicit_self_body (x y : Int) :
    SemSafeCtxA factoryCtx [] .ivar0 (.send (some .self') "new" [.int x, .int y] none)
      (.inst "Point" pointInitSpine) factoryCtx [] .ivar0 := by
  exact SemSafeCtxA.construct (c := point) (d := initDecl) (ps := pointInitParams)
    (SemSafeCtxA.selfRead rfl) (.cons .intLit (.cons .intLit .nil rfl) rfl) rfl point_mem
    (by change initDecl ∈ [initDecl]; simp) rfl (by decide) (by change "Point" ∈ ["Point"]; simp)
    rfl (by simp [pointInitParams, FirstOrder, isAliasTy]) initializer_sem
    (reframeTypesB_sound (by decide)) rfl (callWorldB_sound (by decide))
    (fun name => (constGet?_empty (κ := initializerBodyCtx factoryCtx "Point") rfl name).trans
      (constGet?_empty rfl name).symm) (by simp) (by decide)

theorem class_body_sem : SemSafeCtxA entryCtx [] .ivar0 classBody .sym afterFactory [] .ivar0 := by
  have hi : SemSafeCtxA entryCtx [] .ivar0 (.def' initDecl.name initDecl.params initDecl.body)
      .sym afterInit [] .ivar0 :=
    SemSafeCtxA.initDef (ps := pointInitParams) (Ib := pointInitSpine) (τ := .any)
      rfl rfl (by simp [pointInitParams, FirstOrder, isAliasTy]) rfl (by decide)
      PointClass.definitionInit.sem (by change header ∈ [header]; simp) (by decide)
  have hs : SemSafeCtxA afterInit [] .ivar0 (.defs .self' factory.name factory.params factory.body)
      .sym afterFactory [] .ivar0 :=
    SemSafeCtxA.singletonDecl (ps := []) rfl (by simp) (by decide) (factory_body 0 0) rfl rfl
      (by change initClass ∈ [initClass, header]; simp) (reframeTypesB_sound (by decide)) (by simp)
      rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact hi.seq hs

theorem factory_call : SemSafeCtxA callerCtx [] .ivar0 call (.inst "Point" pointInitSpine)
    callerCtx [] .ivar0 :=
  SemSafeCtxA.singletonCall (c := point) (d := factory) (ps := [])
    (SemSafeCtxA.constClass point_mem) .nil rfl point_mem (by change factory ∈ [factory]; simp)
    (directSendNameB_sound (by decide)) rfl (by simp) (by decide) (factory_body 0 0)
    (ReframeFO.empty rfl rfl rfl rfl) rfl (.main rfl rfl rfl)
    (fun name => (constGet?_empty (κ := factoryCtx) rfl name).trans (constGet?_empty rfl name).symm)
    (by simp)

theorem factory_sem : SemSafeCtxA ctx0 [] .ivar0 program (.inst "Point" pointInitSpine)
    callerCtx [] .ivar0 :=
  (SemSafeCtxA.classDecl class_body_sem (by decide)).seq factory_call

theorem factory_safe (hb : bootOkB = true) : StuckFree bootMachine program :=
  (factory_sem bootMachine (stateOk_boot hb)).1

#guard match Interp.run 500 (evalFrom bootMachine program) with
  | .value (.ref o) m => isExactInst m.heap (.ref o) "Point" &&
      (ivarOf m.heap (.ref o) "@x").identEq (.int 0) &&
      (ivarOf m.heap (.ref o) "@y").identEq (.int 0)
  | _ => false

#print axioms factory_body
#print axioms explicit_self_body
#print axioms factory_sem
#print axioms factory_safe
end Checker.Soundness.Typed.FactoryConstructorControls
