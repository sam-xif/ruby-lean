import Denote.Rules.Expr.Branch
import Denote.Judgment.JudgeA

/-! Truthiness narrowing of a nilable local. The condition is the local itself, so the
branch starts at the unchanged machine whose local now has the refined type. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem denM_not_false {σ : Ty} {m : Machine} (hf : falseFreeB σ = true) :
    ¬ denM σ m (.bool false) := by
  cases σ <;> simp_all [falseFreeB, denM, isIntV, isFltV, isSymV, arrElems?, hshEntries?]

/-- Refining a bound local's type to one its current value inhabits. -/
theorem envOk_refine {Γ : Env} {x : String} {τ σ : Ty} {m : Machine} (h : EnvOk Γ m)
    (hx : envGet? Γ x = some τ) (hσ : denM σ m (m.getLocal x)) (ha : isAliasTy σ = false) :
    EnvOk (envSet Γ x σ) m := by
  refine ⟨?_, ?_⟩
  · intro y ρ hy
    by_cases hyx : y = x
    · subst hyx
      rw [envGet?_envSet_self] at hy
      cases hy
      refine ⟨by cases σ <;> simp_all [stripAlias, isAliasTy], ?_⟩
      intro z ρ' he; subst he; simp [isAliasTy] at ha
    · rw [envGet?_envSet_ne _ _ _ _ hyx] at hy
      exact h.1 y ρ hy
  · intro y hy
    by_cases hyx : y = x
    · subst hyx; rw [envGet?_envSet_self] at hy; cases hy
    · rw [envGet?_envSet_ne _ _ _ _ hyx] at hy
      exact h.2 y hy

theorem SemSafeCtxA.ifTruthy {κ κ' : Ctx} {Γ Γ₁ Γ₂ : Env} {I I' : Ty} {x : String}
    {σ τ₁ τ₂ : Ty} {t e : Ratchet.Expr}
    (hx : envGet? Γ x = some (.nilable σ)) (hf : falseFreeB σ = true) (ha : isAliasTy σ = false)
    (ht : SemSafeCtxA κ (envSet Γ x σ) I t τ₁ κ' Γ₁ I')
    (he : SemSafeCtxA κ (envSet Γ x .nilT) I e τ₂ κ' Γ₂ I') :
    SemSafeCtxA κ Γ I (.if' (.var .lvar x) t (some e)) (joinT τ₁ τ₂) κ' (joinEnv Γ₁ Γ₂) I' := by
  intro m hm
  let k : Kont := .ifK (toRuby t) (some (toRuby e))
  have hv : denM (.nilable σ) m (m.getLocal x) := by
    simpa [stripAlias] using (hm.env.1 x _ hx).1
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m (.var .lvar x))) from rfl)
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next (deliverA (.val (m.getLocal x)) m [k]) from by
    simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl, List.nil_append] using
      step_var_ctl (m := pushK [k] (evalFrom m (.var .lvar x))) (x := x) rfl)
  have hbranch : Interp.stepFn (deliverA (.val (m.getLocal x)) m [k]) =
      .next (evalFrom m (if (m.getLocal x).truthy then t else e)) := by
    simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, k]
    cases hv : (m.getLocal x).truthy <;> simp [hv, Interp.withCtl, evalFrom, toRuby]
  apply RunSpec.step (by rfl) hbranch
  cases htr : (m.getLocal x).truthy
  · -- falsy: the nilable value is nil, since σ excludes false
    have hnil : denM .nilT m (m.getLocal x) := by
      rw [denM] at hv
      rcases hv with hv | hv
      · simpa [denM] using hv
      · cases hg : m.getLocal x with
        | nil => simp [denM, isNilV]
        | bool b =>
          cases b
          · rw [hg] at hv; exact absurd hv (denM_not_false hf)
          · rw [hg] at htr; cases htr
        | _ => rw [hg] at htr; cases htr
    have hs : StateOk κ (envSet Γ x .nilT) I m :=
      { hm with env := envOk_refine hm.env hx hnil rfl }
    simpa only [Bool.false_eq_true, ite_false] using
      (he.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv false hm, denM_joinT_right hd⟩)) m hs
  · have hsv : denM σ m (m.getLocal x) := by
      rw [denM] at hv
      rcases hv with hv | hv
      · cases hg : m.getLocal x <;> rw [hg] at hv htr <;> simp_all [isNilV, Value.truthy]
      · exact hv
    have hs : StateOk κ (envSet Γ x σ) I m :=
      { hm with env := envOk_refine hm.env hx hsv ha }
    simpa only [ite_true] using
      (ht.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv true hm, denM_joinT_left hd⟩)) m hs

#print axioms SemSafeCtxA.ifTruthy
end Ratchet.Denote.Typed
