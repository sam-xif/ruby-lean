import Denote.Typed.ClassHeaderRun
import Denote.Typed.MemberDefine
import Denote.Typed.InitBodyControls
import Denote.Typed.Sequence
import Denote.Typed.ConstructorLookup
import Denote.Typed.InitChecked
import Denote.Typed.ClassRules

/-! The entire 061 class statement, with both method bodies proved from annotations.
Its caller receives installed code and full state, not a constructor-call admission. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.PointClass
open RubyCore Ratchet Ratchet.Denote

def header : Cls := classHeader "Point"
def entryCtx : Ctx := classHeaderCtx (classBodyCtx ctx0 "Point") "Point"
def initDecl : Defn := ⟨"initialize", [.req "x", .req "y"], pointInitBody⟩
def afterInit : Ctx := instanceDeclCtx entryCtx header initDecl
def initClass : Cls := classWithMethod header initDecl
def getter : Defn := ⟨"getX", [], .var .ivar "@x"⟩
def bodyCtx : Ctx := instanceDeclCtx afterInit initClass getter
def callerCtx : Ctx := returnScopeCtx ctx0 bodyCtx
def body : Ratchet.Expr := .seq [.def' initDecl.name initDecl.params initDecl.body,
  .def' getter.name getter.params getter.body]
def program : Ratchet.Expr := .class' "Point" none body

def initBodyHint : Deriv := .seq [
  .ivarAsgn "@x" (.var .lvar "x"), .ivarAsgn "@y" (.var .lvar "y")]
def initHint : Deriv := .defDecl "initialize" pointInitParams .any initBodyHint

def definitionInit : CheckedInitializer (initializerBodyCtx afterInit "Point") initDecl :=
  (checkInitializerBody 80 (initializerBodyCtx afterInit "Point") initDecl initHint).get (by rfl)

def finalInit : CheckedInitializer (initializerBodyCtx callerCtx "Point") initDecl :=
  (refreshInitializerBody 80 (initializerBodyCtx callerCtx "Point") definitionInit initBodyHint).get (by rfl)

theorem body_sem : SemSafeCtxA entryCtx [] .ivar0 body .sym bodyCtx [] .ivar0 := by
  have hi : SemSafeCtxA entryCtx [] .ivar0 (.def' initDecl.name initDecl.params initDecl.body)
      .sym afterInit [] .ivar0 :=
    SemSafeCtxA.initDef (ps := pointInitParams) (Ib := pointInitSpine) (τ := .any)
      rfl rfl (by simp [pointInitParams, FirstOrder, isAliasTy]) rfl (by decide)
      definitionInit.sem (by change header ∈ [header]; simp) (by decide)
  have hg : SemSafeCtxA afterInit [] .ivar0 (.def' getter.name getter.params getter.body)
      .sym bodyCtx [] .ivar0 :=
    SemSafeCtxA.memberDef (ps := []) (Ib := pointInitSpine) (τ := .int)
      rfl (by simp) rfl (by decide) SemSafeCtxA.ivarRead (by decide)
      (by change initClass ∈ [initClass, header]; simp) (by decide)
  exact hi.seq hg

/-- All-fuel class entry/body/exit, retaining arbitrary first-order caller locals. -/
theorem runSpec {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk ctx0 Γ I m)
    (hI : FirstOrder I = true) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) :
    RunSpec m (evalFrom m program) Γ .sym callerCtx I := by
  have ht : reframeTypesB (returnScopeCtx ctx0 bodyCtx) I = true := by
    change FirstOrder I && true && true && true = true
    simp [hI]
  have hg : localTypesB Γ = true := List.all_eq_true.mpr hΓ
  exact (SemSafeCtxA.classDecl body_sem (by
    simp only [classRuleB, ht, hg, Bool.true_and]
    decide)) m hm

theorem main_guard {Γ : Env} {I : Ty} (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) : mainCallB callerCtx Γ I = true := by
  have ht : reframeTypesB callerCtx I = true := by
    change FirstOrder I && true && true && true = true
    simp [hI]
  have hg : localTypesB Γ = true := List.all_eq_true.mpr hΓ
  rw [mainCallB, ht, hg]
  rfl

/-- Recheck the initializer under the final published table, after getX was installed.
This is an annotation-domain proof, not a cast of the earlier definition's context. -/
theorem initializer_body :
    SemInitA (initializerBodyCtx callerCtx "Point") pointInitParams .ivar0 pointInitBody .any
      (initializerBodyCtx callerCtx "Point") pointInitParams pointInitSpine :=
  finalInit.sem

theorem getter_body :
    SemSafeCtxA (instanceBodyCtx callerCtx ⟨"Point", "Point", "getX"⟩ pointInitSpine)
      [] pointInitSpine getter.body .int
      (instanceBodyCtx callerCtx ⟨"Point", "Point", "getX"⟩ pointInitSpine) [] pointInitSpine :=
  SemSafeCtxA.ivarRead

theorem constructor_code {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk callerCtx Γ I m) :
    ∃ k md, InstanceSite callerCtx "Point" k m.heap ∧
      NewDispatch m.heap (classOf m.heap (.ref k)) ∧
      md.params = [.req "x", .req "y"] ∧ md.body = toRuby pointInitBody ∧
      InstanceMethodCode k "initialize" md ∧ Interp.userInit? m.heap k = some md :=
  declared_constructor_code (c := classWithMethod initClass getter) (d := initDecl) hm
    (by change classWithMethod initClass getter ∈ [classWithMethod initClass getter, initClass, header]; simp)
    (by change initDecl ∈ [getter, initDecl]; simp) rfl (by decide)

#print axioms body_sem
#print axioms runSpec
#print axioms initializer_body
#print axioms getter_body
end Ratchet.Denote.Typed.PointClass
