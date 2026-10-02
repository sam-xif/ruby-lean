import Denote.Judgment.BoundedRun

/-! `while c do b end` with a loop-invariant context: the condition and the body both
return the incoming locals, context and spine. Each re-entry pays one machine step, so
the bounded contract is proved by induction on the step budget. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- A raise reaching a loop continuation is propagated unchanged. -/
theorem step_loop_raise {m : Machine} {k : Kont} {c b : RubyCore.Expr} {exc : Value}
    (hk : k = .whileCondK c b ∨ k = .whileBodyK c b) :
    Interp.stepFn (deliverA (.esc (.raiseJ exc)) m [k]) = .next (deliverA (.esc (.raiseJ exc)) m []) := by
  rcases hk with rfl | rfl <;> rfl

theorem while_loop {κ : Ctx} {Γ : Env} {I σ τ : Ty} {c b : Ratchet.Expr}
    (hc : SemSafeCtxA κ Γ I c σ κ Γ I) (hb : SemSafeCtxA κ Γ I b τ κ Γ I) :
    ∀ N m, StateOk κ Γ I m →
      RunSpecAt N m (pushK [.whileCondK (toRuby c) (toRuby b)] (evalFrom m c)) Γ .nilT κ I := by
  intro N
  induction N with
  | zero => intro m _; exact RunSpecAt.zero (by simp [answerPoint, pushK, evalFrom])
  | succ N ih =>
    intro m hm
    apply ((hc m hm).at (N + 1)).bindSpec hm.rootClean (by intro k hk; simp at hk; subst hk; rfl)
    intro a n hr
    cases a with
    | esc j =>
      obtain ⟨exc, rfl, _⟩ := EscOk.only_raise hr.2.1
      apply RunSpecAt.stepWithin (by rfl) (step_loop_raise (.inl rfl))
      exact RunSpecAt.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩
    | val v =>
      have hn := hr.2.2 v rfl
      cases hv : v.truthy
      · apply RunSpecAt.stepWithin (next := deliverA (.val .nil) n []) (by rfl) (by
          simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, hv,
            Bool.false_eq_true, ↓reduceIte, Interp.withCtl])
        exact RunSpecAt.answer ⟨hr.1, by simp [AnsOk, denM, isNilV],
          fun _ he => by cases he; exact hn⟩
      · apply RunSpecAt.step (next := pushK [.whileBodyK (toRuby c) (toRuby b)] (evalFrom n b)) (by rfl)
          (by simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, hv, ↓reduceIte,
                Interp.withKont, pushK, evalFrom, List.nil_append])
        apply ((hb n hn).at N).bindSpec (origin := m) hn.rootClean
          (by intro k hk; simp at hk; subst hk; rfl)
        intro a' n' hr'
        cases a' with
        | esc j =>
          obtain ⟨exc, rfl, _⟩ := EscOk.only_raise hr'.2.1
          apply RunSpecAt.stepWithin (by rfl) (step_loop_raise (.inr rfl))
          exact RunSpecAt.answer ⟨hr.1.trans hr'.1, hr'.2.1, fun _ hv => by cases hv⟩
        | val w =>
          have hn' := hr'.2.2 w rfl
          apply RunSpecAt.stepWithin (next := pushK [.whileCondK (toRuby c) (toRuby b)] (evalFrom n' c))
            (by rfl) (by
              simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, Interp.withKont,
                pushK, evalFrom, List.nil_append])
          exact (ih n' hn').rebase (hr.1.trans hr'.1)

theorem SemSafeCtxA.while' {κ : Ctx} {Γ : Env} {I σ τ : Ty} {c b : Ratchet.Expr}
    (hc : SemSafeCtxA κ Γ I c σ κ Γ I) (hb : SemSafeCtxA κ Γ I b τ κ Γ I) :
    SemSafeCtxA κ Γ I (.while' c b) .nilT κ Γ I := by
  intro m hm
  apply runSpec_iff_allAt.mpr
  intro N
  exact RunSpecAt.stepWithin (answerPoint_evalFrom _ _) (show Interp.stepFn _ =
    .next (pushK [.whileCondK (toRuby c) (toRuby b)] (evalFrom m c)) from rfl) (while_loop hc hb N m hm)

#print axioms SemSafeCtxA.while'
end Ratchet.Denote.Typed
