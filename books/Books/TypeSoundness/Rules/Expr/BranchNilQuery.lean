import Books.TypeSoundness.Rules.Expr.BranchNarrow
import Books.TypeSoundness.Rules.Primitive.PrimitiveBuiltin
import Books.TypeSoundness.Judgment.RunWith

/-! `if x.nil?` narrowing of a nilable Integer local. The query runs the native
NilClass#nil?/Object#nil? row, so its Boolean result is exactly the local's nil-ness. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem nil_nil_run (m : Machine) :
    Builtins.run "NilClass#nil?" .nil [] m = .ok (.bool true) m := by
  simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
    Builtins.strPayload?, Builtins.complexEqualityImpure, Bool.false_or, Bool.or_false,
    Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The condition's result records the local's nil-ness at an unchanged local. -/
theorem nilQuery_cond {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {x : String}
    (hm : StateOk κ Γ I m) (hv : m.getLocal x = .nil ∨ ∃ i, m.getLocal x = .int i)
    (hfree : nameFreeN κ "nil?" = true) :
    RunWith m (evalFrom m (.send (some (.var .lvar x)) "nil?" [] none)) Γ .bool κ I
      (fun v n => v = .bool (isNilV (m.getLocal x)) ∧ n.getLocal x = m.getLocal x) := by
  let k : Kont := .recvK "nil?" [] .none .explicit
  apply RunWith.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m (.var .lvar x))) from rfl)
  apply RunWith.step (by rfl) (show Interp.stepFn _ = .next (deliverA (.val (m.getLocal x)) m [k]) from by
    simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl, List.nil_append] using
      step_var_ctl (m := pushK [k] (evalFrom m (.var .lvar x))) (x := x) rfl)
  let M := deliverA (.val (m.getLocal x)) m []
  have hM : StateOk κ Γ I M := StateOk_deliverA hm
  have hinv : Interp.stepFn (deliverA (.val (m.getLocal x)) m [k]) =
      Interp.invoke M (m.getLocal x) .explicit "nil?" [] none [] := rfl
  have hans : ∀ b, b = isNilV (m.getLocal x) →
      Interp.invoke M (m.getLocal x) .explicit "nil?" [] none [] = .next (Interp.withCtl M (.value (.bool b))) →
      RunWith m (deliverA (.val (m.getLocal x)) m [k]) Γ .bool κ I
        (fun v n => v = .bool (isNilV (m.getLocal x)) ∧ n.getLocal x = m.getLocal x) := by
    intro b hb hstep
    apply RunWith.step (by rfl) (hinv.trans hstep)
    apply RunWith.answer (a := .val (.bool b)) (m := M)
      (fun v n c ks hp => ⟨hp.1, by rw [getLocal_reCtl]; exact hp.2⟩)
    exact ⟨⟨Framed_reCtl m _ [], by simp [AnsOk, denM, isBoolV], fun _ _ => hM⟩,
      fun v hv => by cases hv; exact ⟨by rw [hb], getLocal_reCtl m _ [] x⟩⟩
  rcases hv with hn | ⟨i, hi⟩
  · apply hans true (by rw [hn]; rfl)
    rw [hn, primitive_invoke (bid := "NilClass#nil?") (k := Boot.nilClassId) hM
      (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl) hfree,
      nil_nil_run]
    rfl
  · apply hans false (by rw [hi]; rfl)
    rw [hi, primitive_invoke (bid := "Object#nil?") (k := Boot.integerId) hM
      (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl) hfree,
      int_nil_run]
    rfl

#print axioms nilQuery_cond

theorem SemSafeCtxA.ifNilQueryNil {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {x : String}
    {t : Checker.Expr} {e : Option Checker.Expr}
    (hx : envGet? Γ x = some .nilT) (hfree : nameFreeN κ "nil?" = true)
    (ht : SemSafeCtxA κ Γ I t τ κ' Γ' I') :
    SemSafeCtxA κ Γ I (.if' (.send (some (.var .lvar x)) "nil?" [] none) t e) τ κ' Γ' I' := by
  intro m hm
  let k : Kont := .ifK (toRuby t) (e.map toRuby)
  have hnil : m.getLocal x = .nil := by
    have h := (hm.env.1 x _ hx).1
    simp only [stripAlias, denM] at h
    cases hg : m.getLocal x <;> rw [hg] at h <;> simp_all [isNilV]
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m (.send (some (.var .lvar x)) "nil?" [] none))) from by
      cases e <;> rfl)
  apply (nilQuery_cond hm (.inl hnil) hfree).bindSpec hm.rootClean (by intro c hc; simp at hc; subst hc; rfl)
  intro a n hr
  cases a with
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hr.1.1, hr.1.2.1, fun _ hv => by cases hv⟩
  | val w =>
    obtain ⟨hw, _⟩ := hr.2 w rfl
    subst hw
    have hn : StateOk κ Γ I n := hr.1.2.2 _ rfl
    have hbranch : Interp.stepFn (deliverA (.val (.bool (isNilV (m.getLocal x)))) n [k]) =
        .next (evalFrom n t) := by
      simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, k, hnil]
      simp [isNilV, Value.truthy, Interp.withCtl, evalFrom]
    apply RunSpec.step (by rfl) hbranch
    exact RunSpec.rebase (ht n hn) hr.1.1

#print axioms SemSafeCtxA.ifNilQueryNil
end Checker.Soundness.Typed
