import Denote.Typed.ConstructorExpr
import Denote.Typed.ClassConstant
import Denote.Typed.ClassHeaderRun
import Denote.Typed.MemberDefine
import Denote.Typed.InitExpr
import Denote.Typed.Sequence
import Denote.Typed.InitChecked
import Denote.Sanity

/-! A second class, independent of Point: one Boolean parameter, Boolean initializer
result, no fields. The same generic constructor returns the instance, not that Boolean. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.FlagBox
open RubyCore Ratchet Ratchet.Denote

def header : Cls := classHeader "FlagBox"
def entryCtx : Ctx := classHeaderCtx (classBodyCtx ctx0 "FlagBox") "FlagBox"
def init : Defn := ⟨"initialize", [.req "flag"], .var .lvar "flag"⟩
def params : Env := [("flag", .bool)]
def bodyCtx : Ctx := instanceDeclCtx entryCtx header init
def callerCtx : Ctx := returnScopeCtx ctx0 bodyCtx
def body : Ratchet.Expr := .def' init.name init.params init.body
def program : Ratchet.Expr := .class' "FlagBox" none body

private def hint : Deriv := .defDecl "initialize" params .bool (.var .lvar "flag")
def definitionInit : CheckedInitializer (initializerBodyCtx bodyCtx "FlagBox") init :=
  (checkInitializerBody 40 (initializerBodyCtx bodyCtx "FlagBox") init hint).get (by rfl)
def finalInit : CheckedInitializer (initializerBodyCtx callerCtx "FlagBox") init :=
  (refreshInitializerBody 40 (initializerBodyCtx callerCtx "FlagBox") definitionInit
    (.var .lvar "flag")).get (by rfl)

-- The body proof is generic in its whole context; no call value appears in it.
theorem initializer_body {κ : Ctx} : SemInitA κ params .ivar0 init.body .bool κ params .ivar0 :=
  SemInitA.var rfl rfl

theorem body_sem : SemSafeCtxA entryCtx [] .ivar0 body .sym bodyCtx [] .ivar0 := by
  have ht : ReframeFO entryCtx .ivar0 := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro τ h; cases h; rfl
    · intro τ h; cases h
    · intro x τ h; rw [constGet?_empty (κ := entryCtx) rfl x] at h; cases h
    · intro x τ h; cases h
  exact SemSafeCtxA.initializerDecl (ps := params) (Ib := .ivar0) (τ := .bool)
    rfl rfl (by simp [params, FirstOrder, isAliasTy]) rfl rfl definitionInit.sem rfl
    (by change header ∈ [header]; simp) ht (by simp) rfl
    (by decide) (by decide) (by decide) (by decide)

theorem class_run {m : Machine} (hm : StateOk ctx0 [] .ivar0 m) :
    RunSpec m (evalFrom m program) [] .sym callerCtx .ivar0 :=
  class_header_runSpec hm (ReframeFO.empty rfl rfl rfl rfl) rfl rfl rfl rfl rfl rfl rfl
    (fun _ => rfl) (by simp) rfl (ClassTablesFrame.empty rfl rfl) (by decide) (by decide) (by decide)
    rfl (by constructor <;> decide) (by decide) (by decide) body_sem

def newExpr : Ratchet.Expr := .send (some (.const "FlagBox")) "new" [.tru] none

theorem new_sem : SemSafeCtxA callerCtx [] .ivar0 newExpr
    (.inst "FlagBox" .ivar0) callerCtx [] .ivar0 := by
  have hc : classWithMethod header init ∈ callerCtx.classes := by
    change classWithMethod header init ∈ [classWithMethod header init, header]; simp
  have hr := SemSafeCtxA.constClass (Γ := []) (I := .ivar0) hc
  exact hr.construct (d := init) (ps := params) (.cons .truLit .nil rfl) rfl hc
    (by change init ∈ [init]; simp) rfl (by decide)
    (by change "FlagBox" ∈ ["FlagBox"]; simp) rfl
    (by simp [params, FirstOrder, isAliasTy]) finalInit.sem
    (ReframeFO.empty rfl rfl rfl rfl) rfl rfl rfl rfl
    (fun x => (constGet?_empty (κ := initializerBodyCtx callerCtx "FlagBox") rfl x).trans
      (constGet?_empty rfl x).symm) (by simp) rfl

theorem class_new_run (hb : bootOkB = true) :
    RunSpec bootMachine (evalFrom bootMachine (.seq [program, newExpr])) []
      (.inst "FlagBox" .ivar0) callerCtx .ivar0 :=
  (class_run (stateOk_boot hb)).thenSeq (.last new_sem)

#guard match Interp.run 150 (evalFrom bootMachine (.seq [program, newExpr])) with
  | .value (.ref o) n => isExactInst n.heap (.ref o) "FlagBox" && (n.heap.get o).ivars.isEmpty
  | _ => false

#print axioms initializer_body
#print axioms class_new_run
end Ratchet.Denote.Typed.FlagBox
