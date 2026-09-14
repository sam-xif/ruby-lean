import Denote.Typed.JudgeA

/-! Composition for the answer-typed rules. The existing continuation typing admits only
assignment frames; its escape clause and `run_pushK` lift an answer-correct, safe closed run
to every continuation it admits. This preserves `SafeUnder` as the registration target. -/

set_option autoImplicit false

namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem DKontOk.catchFree {τa τ : Ty} {K : List Kont} {Γ : Env}
    (hk : DKontOk τa K Γ τ) : RubyCore.Proof.CatchFree K := by
  induction hk with
  | nil => simp [RubyCore.Proof.CatchFree]
  | asgnK _ _ _ ih =>
    simpa [RubyCore.Proof.CatchFree] using ih

theorem safeA_escape_kontOk {τa τ : Ty} {K : List Kont} {Γ : Env}
    (hk : DKontOk τa K Γ τ) :
    ∀ (m : Machine) (j : Jump), EscOk m j → SafeA (deliverA (.esc j) m K) := by
  induction hk with
  | nil =>
    intro m j hj fuel
    cases fuel with
    | zero => rfl
    | succ f =>
      cases j <;>
        simp_all [EscOk, Interp.run, Interp.stepFn, deliverA, Answer.ctl,
          Interp.unwind, Semantics.typeStuck]
  | @asgnK rest Γ τ x _ _ _ ih =>
    intro m j hj fuel
    cases fuel with
    | zero => rfl
    | succ f =>
      rw [run_succ, step_asgnK_jump rfl rfl]
      exact ih m j hj f

/-- The whole-run safety premise handles halts; the answer premise handles the value and
escape delivered to the continuation. Neither premise alone is sufficient. -/
theorem safeUnder_of_closed {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (ha : SemJudgeA Γ e τ Γ')
    (hs : ∀ m, StateOk ctx0 Γ .ivar0 m → StuckFree m e) : SafeUnder Γ e τ Γ' := by
  intro τa m hm hc hk
  have hbase : pushK m.kont (evalFrom m e) = m := by
    simp [pushK, evalFrom, ← hc]
  rw [← hbase]
  apply safe_pushK hk.catchFree haltBlind_stuck oof_stuck (hs m hm)
  · exact fun fuel a m₀ rest hr => (ha m hm fuel a m₀ rest hr).2
  · intro a m₀ hp fuel
    rcases hp with ⟨hd, hm₀⟩
    cases a with
    | val v =>
      exact safeA_value_kontOk hk (m := deliverA (.val v) m₀ m.kont) rfl rfl
        (StateOk_deliverA (hm₀ v rfl))
        (denM_deliverA.mpr hd) fuel
    | esc j => exact safeA_escape_kontOk hk m₀ j hd fuel

theorem SemSafeA.closed {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : SemSafeA Γ e τ Γ') {m : Machine} (hm : StateOk ctx0 Γ .ivar0 m) :
    StuckFree m e :=
  h.2 τ (evalFrom m e) (StateOk_reCtl hm _ _) rfl .nil

/-- Change the result contract using a semantic implication, preserving the safety claim. -/
theorem SemSafeA.weaken {Γ Γ₁ Γ₂ : Env} {e : Ratchet.Expr} {σ τ : Ty}
    (h : SemSafeA Γ e σ Γ₁)
    (hout : ∀ m v, StateOk ctx0 Γ₁ .ivar0 m → denM σ m v →
      StateOk ctx0 Γ₂ .ivar0 m ∧ denM τ m v) : SemSafeA Γ e τ Γ₂ := by
  have ha : SemJudgeA Γ e τ Γ₂ := by
    intro m hm fuel a m₀ rest hr
    obtain ⟨hf, hd, hs⟩ := h.1 m hm fuel a m₀ rest hr
    refine ⟨hf, ?_, ?_⟩
    · cases a with
      | val v => exact (hout m₀ v (hs v rfl) hd).2
      | esc j => exact hd
    · intro v hv
      subst hv
      exact (hout m₀ v (hs v rfl) hd).1
  exact ⟨ha, safeUnder_of_closed ha (fun _ hm => h.closed hm)⟩

/-- A frame evaluates one premise, selects the next expression on a value, and propagates
escapes. All three step equations are premises about the actual machine. -/
theorem semSafe_frame {Γ Γ₁ Γ₂ : Env} {sub out : Ratchet.Expr} {σ τ : Ty}
    {k : Kont} {branch : Value → Ratchet.Expr}
    (hp : SemSafeA Γ sub σ Γ₁)
    (hb : ∀ v, SemSafeA Γ₁ (branch v) τ Γ₂)
    (hK : RubyCore.Proof.CatchFree [k])
    (heval : ∀ m, Interp.stepFn (evalFrom m out) =
      .next (pushK [k] (evalFrom m sub)))
    (hval : ∀ m v, Interp.stepFn (deliverA (.val v) m [k]) =
      .next (evalFrom m (branch v)))
    (hesc : ∀ m j, Interp.stepFn (deliverA (.esc j) m [k]) =
      .next (deliverA (.esc j) m [])) : SemSafeA Γ out τ Γ₂ := by
  have hap : ∀ a m, answerPoint (deliverA a m [k]) = none := by
    intro a m; simp [answerPoint, deliverA]
  have ha : SemJudgeA Γ out τ Γ₂ := by
    intro m hm fuel a m₀ rest hr
    cases fuel with
    | zero => rw [runA_zero (answerPoint_evalFrom m out)] at hr; cases hr
    | succ f =>
      rw [runA_succ (answerPoint_evalFrom m out), heval] at hr
      simp only at hr
      rw [runA_pushK _ hK] at hr
      cases hs : runA f (evalFrom m sub) with
      | halt h => rw [hs] at hr; cases h <;> cases hr
      | oof n => rw [hs] at hr; cases hr
      | ans a₁ m₁ r₁ =>
        rw [hs] at hr
        obtain ⟨hf, hd, hm₁⟩ := hp.1 m hm f a₁ m₁ r₁ hs
        change runA r₁ (deliverA a₁ m₁ [k]) = .ans a m₀ rest at hr
        cases r₁ with
        | zero => rw [runA_zero (hap _ _)] at hr; cases hr
        | succ g =>
          rw [runA_succ (hap _ _)] at hr
          cases a₁ with
          | val v =>
            rw [hval] at hr
            obtain ⟨hf₂, hd₂, hm₂⟩ := (hb v).1 m₁ (hm₁ v rfl) g a m₀ rest hr
            exact ⟨hf.trans hf₂, hd₂, hm₂⟩
          | esc j =>
            rw [hesc] at hr
            simp only at hr
            rw [runA_ans (a := .esc j) (by simp [answerPoint, deliverA, Answer.ctl])] at hr
            injection hr with h₁ h₂
            cases h₁; cases h₂
            refine ⟨hf.trans (Framed_reCtl _ _ _), ?_, ?_⟩
            · cases j <;> simpa [AnsOk, EscOk, deliverA] using hd
            · intro v hv; cases hv
  refine ⟨ha, safeUnder_of_closed ha ?_⟩
  intro m hm fuel
  cases fuel with
  | zero => rfl
  | succ f =>
    rw [run_succ, heval]
    apply safe_pushK hK haltBlind_stuck oof_stuck (hp.closed hm)
      (fun f a n r hr => (hp.1 m hm f a n r hr).2) ?_ f
    intro a n hn g
    cases g with
    | zero => rfl
    | succ g =>
      rw [run_succ]
      cases a with
      | val v =>
        rw [hval]
        exact (hb v).closed (hn.2 v rfl) g
      | esc j =>
        rw [hesc]
        exact safeA_escape_kontOk (DKontOk.nil (τa := τ) (Γ := Γ₂)) n j hn.1 g

#print axioms safeUnder_of_closed
#print axioms semSafe_frame

end Ratchet.Denote.Typed
