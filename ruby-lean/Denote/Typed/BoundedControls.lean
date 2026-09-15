import Denote.Typed.BoundedCall
import Denote.Typed.MethodDefine
import Denote.Typed.MethodCall
import Denote.Typed.Sequence

/-! Guard controls and a recursive semantic pilot, now also admitted by a body certificate. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- A value is already an answer at zero fuel; its annotation is not vacuous. -/
theorem bounded_zero_checks_answer (m : Machine) :
    ¬ RunSpecAt 0 m (deliverA (.val (.bool true)) m []) [] .int ctx0 .ivar0 := by
  intro h
  have hr := h.2 0 (Nat.le_refl _) (.val (.bool true))
    (deliverA (.val (.bool true)) m []) 0 (runA_ans rfl 0)
  have hv := hr.2.1
  simp [AnsOk, denM, isIntV] at hv

-- Conversely, an unevaluated expression has no answer at zero fuel. No finite bound
-- alone is used to admit a body: the recursive rule must prove every bound.
example (m : Machine) : RunSpecAt 0 m
    (evalFrom m (.send (some (.int 1)) "+" [.str "bad"] none)) [] .int ctx0 .ivar0 :=
  RunSpecAt.zero (answerPoint_evalFrom _ _)

private def spinDecl : Defn := ⟨"spin", [.req "x"], .send none "spin" [.var .lvar "x"] none⟩
private def spinParams : Env := [("x", .int)]
private def spinCtx : Ctx := topBodyCtx ctx0 spinDecl

/-- Tie the actual recursive call by decreasing execution fuel, for every annotated input.
No claim of termination: this pilot deliberately has no returned values. -/
theorem spin_body_sem : SemSafeCtxA spinCtx spinParams .ivar0 spinDecl.body .int
    spinCtx spinParams .ivar0 := by
  apply semSafeCtxA_of_guarded
  intro N ih
  cases N with
  | zero => exact SemSafeCtxAt.zero
  | succ n =>
    exact SemSafeCtxAt.callSig (decl := spinDecl) (ps := spinParams) rfl
      (by simp [spinParams, FirstOrder, isAliasTy]) rfl (ih n (Nat.lt_succ_self _))
      (.cons ((SemSafeCtxA.var rfl rfl).at n) .nil rfl)
      (by change spinDecl ∈ [spinDecl]; simp) rfl rfl rfl rfl rfl rfl rfl
      (by simp [spinParams, FirstOrder, stripAlias])

private def spinProgram : Ratchet.Expr :=
  .seq [.def' spinDecl.name spinDecl.params spinDecl.body, .send none "spin" [.int 0] none]

theorem spin_program_sem : SemSafeCtxA ctx0 [] .ivar0 spinProgram .int
    (topDeclCtx ctx0 spinDecl) [] .ivar0 := by
  have hd : SemSafeCtxA ctx0 [] .ivar0 (.def' spinDecl.name spinDecl.params spinDecl.body) .sym
      (topDeclCtx ctx0 spinDecl) [] .ivar0 :=
    SemSafeCtxA.defDecl rfl (by simp [spinParams, FirstOrder, isAliasTy]) rfl spin_body_sem
      rfl rfl rfl rfl rfl rfl rfl (by simp) (by simp [ctx0, Ctx.defs]) (by decide) (by decide)
  have hc : SemSafeCtxA (topDeclCtx ctx0 spinDecl) [] .ivar0
      (.send none spinDecl.name [.int 0] none) .int (topDeclCtx ctx0 spinDecl) [] .ivar0 :=
    SemSafeCtxA.callSig rfl (by simp [spinParams, FirstOrder, isAliasTy]) rfl spin_body_sem
      (.cons .intLit .nil rfl)
      (by change spinDecl ∈ [spinDecl]; simp) rfl rfl rfl rfl rfl rfl rfl (by simp)
  exact SemSafeCtxA.sequence (.cons hd (.last hc))

theorem spin_program_safe (hb : bootOkB = true) : StuckFree bootMachine spinProgram :=
  spin_program_sem.closed (stateOk_boot hb)

-- The finite scoped derivation closes the recursive hypothesis; the signature alone cannot.
#guard validateD spinProgram (.seq [
  .defDecl "spin" spinParams .int (.callSig "spin" [.var .lvar "x"] .int),
  .callSig "spin" [.intLit 0] .int])

#print axioms bounded_zero_checks_answer
#print axioms spin_body_sem
#print axioms spin_program_safe
end Ratchet.Denote.Typed
