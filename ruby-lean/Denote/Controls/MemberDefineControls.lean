import Denote.Rules.Instance.MemberDefine
import Denote.Controls.ClassHeaderControls
import Denote.Controls.InitBodyControls
import Denote.Rules.Method.MethodChecked

/-! Annotation-domain definition controls, plus actual class/constructor/member calls.
Class-rule/certificate admission is still gated; code metadata is never a body proof. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def point : Cls := classHeader "Point"
private def scope : Ctx := classHeaderCtx (classBodyCtx ctx0 "Point") "Point"
private def initDecl : Defn := ⟨"initialize", [.req "x", .req "y"], pointInitBody⟩
private def initOut : Ctx := instanceDeclCtx scope point initDecl

private theorem scope_types : ReframeFO scope .ivar0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro τ ht; change some (.clsOf "Point") = some τ at ht; cases ht; rfl
  · intro τ ht; cases ht
  · intro x τ ht; rw [constGet?_empty rfl x] at ht; cases ht
  · intro x τ ht; cases ht

theorem point_initializer_definition :
    SemSafeCtxA scope [] .ivar0 (.def' initDecl.name initDecl.params initDecl.body) .sym
      initOut [] .ivar0 :=
  SemSafeCtxA.initializerDecl (ps := pointInitParams) (Ib := pointInitSpine) (τ := .any)
    rfl rfl (by simp [pointInitParams, FirstOrder, isAliasTy]) rfl (by decide)
    (point_initializer_sem rfl rfl rfl) rfl (by change point ∈ [point]; simp)
    scope_types (by simp) rfl (by decide) (by decide) (by decide) (by decide)

theorem point_initializer_at_entry (hb : bootOkB = true)
    (hn : constOwn bootMachine.heap Boot.objectId "Point" = none) :
    ∃ n, Interp.stepFn (evalFrom bootMachine
      (.class' "Point" none (.def' initDecl.name initDecl.params initDecl.body))) = .next n ∧
      StateOk scope [] .ivar0 n ∧
      RunSpec n (evalFrom n (.def' initDecl.name initDecl.params initDecl.body)) [] .sym initOut .ivar0 := by
  obtain ⟨n, hs, hm⟩ := boot_point_header hb hn (.def' initDecl.name initDecl.params initDecl.body)
  exact ⟨n, hs, hm, point_initializer_definition n hm⟩

private def inc : Defn := ⟨"inc", [.req "x"], .send (some (.var .lvar "x")) "+" [.int 1] none⟩
private def incOut : Ctx := instanceDeclCtx scope point inc
private def incCtx : Ctx := instanceBodyCtx incOut ⟨"Point", "Point", "inc"⟩ .ivar0
private def hint : Deriv := .prim (.var .lvar "x") "+" [.intLit 1] .int .int
private def cert : Deriv := .defDecl "inc" [("x", .int)] .int hint
private def checked : CheckedBody incCtx .ivar0 inc :=
  (checkMethodBody 100 incCtx .ivar0 inc cert).get (by decide)

-- The body is checked before any call, using the entire annotated parameter domain.
#guard (checkMethodBody 100 incCtx .ivar0 inc cert).isSome
#guard (checkMethodBody 100 incCtx .ivar0 inc
  (.defDecl "inc" [("x", .nilable .int)] .int hint)).isNone
#guard (checkMethodBody 100 incCtx .ivar0 inc
  (.defDecl "inc" [("x", .int)] .bool hint)).isNone

theorem inc_member_definition :
    SemSafeCtxA scope [] .ivar0 (.def' inc.name inc.params inc.body) .sym incOut [] .ivar0 :=
  SemSafeCtxA.memberDecl (Ib := .ivar0) checked.paramShape checked.paramsFO checked.returnFO rfl
    (checked_body_context checked) (by decide) rfl (by change point ∈ [point]; simp)
    scope_types (by simp) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- The same method name at another provably distinct heap owner remains legal.
private def other : Cls := classWithMethod (classHeader "Other") inc
#guard memberFreshB { scope with pos := { scope.pos with classes := [point, other] } } point inc
#guard memberTableFrameB [point, other] point inc
#guard !memberFreshB incOut point inc
#guard !classApartB [{ point with super? := some "Missing" }] [] "Point" "Other"

-- Real define+call controls, including a same-name method at another class.
#guard match Interp.run 300 (evalFrom bootMachine (.seq [
    .class' "Other" none (.def' "inc" [] (.int 9)),
    .class' "Point" none (.def' inc.name inc.params inc.body),
    .send (some (.send (some (.const "Point")) "new" [] none)) "inc" [.int 3] none])) with
  | .value (.int 4) _ => true
  | _ => false

#guard match Interp.run 300 (evalFrom bootMachine (.seq [
    .class' "Point" none (.seq [.def' initDecl.name initDecl.params initDecl.body,
      .def' "getX" [] (.var .ivar "@x")]),
    .send (some (.send (some (.const "Point")) "new" [.int 7, .int 8] none)) "getX" [] none])) with
  | .value (.int 7) _ => true
  | _ => false

#print axioms point_initializer_definition
#print axioms point_initializer_at_entry
#print axioms inc_member_definition
end Ratchet.Denote.Typed
