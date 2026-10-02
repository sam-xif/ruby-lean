import Denote.Rules.Expr.BranchNarrow
import Denote.Rules.Primitive.PrimitiveBuiltin
import Denote.Judgment.RunWith

/-! `if x.nil?` narrowing of a nilable Integer local. The query runs the native
NilClass#nil?/Object#nil? row, so its Boolean result is exactly the local's nil-ness. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

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

theorem SemSafeCtxA.ifNilQuery {κ κ' : Ctx} {Γ Γ₁ Γ₂ : Env} {I I' : Ty} {x : String}
    {τ₁ τ₂ : Ty} {t e : Ratchet.Expr}
    (hx : envGet? Γ x = some (.nilable .int)) (hfree : nameFreeN κ "nil?" = true)
    (ht : SemSafeCtxA κ (envSet Γ x .nilT) I t τ₁ κ' Γ₁ I')
    (he : SemSafeCtxA κ (envSet Γ x .int) I e τ₂ κ' Γ₂ I') :
    SemSafeCtxA κ Γ I (.if' (.send (some (.var .lvar x)) "nil?" [] none) t (some e))
      (joinT τ₁ τ₂) κ' (joinEnv Γ₁ Γ₂) I' := by
  intro m hm
  let k : Kont := .ifK (toRuby t) (some (toRuby e))
  have hv0 : denM (.nilable .int) m (m.getLocal x) := by
    simpa [stripAlias] using (hm.env.1 x _ hx).1
  have hv : m.getLocal x = .nil ∨ ∃ i, m.getLocal x = .int i := by
    rw [denM] at hv0
    rcases hv0 with h | h
    · left; cases hg : m.getLocal x <;> rw [hg] at h <;> simp_all [isNilV]
    · right; cases hg : m.getLocal x <;> rw [hg] at h <;> simp_all [denM, isIntV]
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m (.send (some (.var .lvar x)) "nil?" [] none))) from rfl)
  apply (nilQuery_cond hm hv hfree).bindSpec hm.rootClean (by intro c hc; simp at hc; subst hc; rfl)
  intro a n hr
  cases a with
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hr.1.1, hr.1.2.1, fun _ hv => by cases hv⟩
  | val w =>
    obtain ⟨hw, hloc⟩ := hr.2 w rfl
    subst hw
    have hn : StateOk κ Γ I n := hr.1.2.2 _ rfl
    have hbranch : Interp.stepFn (deliverA (.val (.bool (isNilV (m.getLocal x)))) n [k]) =
        .next (evalFrom n (if isNilV (m.getLocal x) then t else e)) := by
      simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, k]
      cases hb : isNilV (m.getLocal x) <;> simp [Value.truthy, Interp.withCtl, evalFrom, toRuby]
    apply RunSpec.step (by rfl) hbranch
    apply RunSpec.rebase _ hr.1.1
    cases hb : isNilV (m.getLocal x)
    · have hint : denM .int n (n.getLocal x) := by
        rw [hloc]
        rcases hv with h | ⟨i, h⟩
        · rw [h] at hb; cases hb
        · rw [h]; simp [denM, isIntV]
      have hs : StateOk κ (envSet Γ x .int) I n := { hn with env := envOk_refine hn.env hx hint rfl }
      simpa only [Bool.false_eq_true, ite_false] using
        (he.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv false hm, denM_joinT_right hd⟩)) n hs
    · have hnil : denM .nilT n (n.getLocal x) := by
        rw [hloc]; simpa [denM] using hb
      have hs : StateOk κ (envSet Γ x .nilT) I n := { hn with env := envOk_refine hn.env hx hnil rfl }
      simpa only [ite_true] using
        (ht.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv true hm, denM_joinT_left hd⟩)) n hs

#print axioms SemSafeCtxA.ifNilQuery
end Ratchet.Denote.Typed
