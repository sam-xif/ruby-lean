import Denote.Rules.Expr.CaseEq

/-! `if x && c` on a nilable local, as desugared: `if (t = x; if t then c else t)`.
The temporary aliases `x` (`vasgnAlias`); a truthy `t` refines both names for `c` and the
then branch, and the else branch runs after either a falsy `c` or a nil `x`. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.ifAndVar {κ κ' : Ctx} {Γ Γc Γ₁ Γ₂ : Env} {I I' : Ty} {x t : String}
    {σ τc τ₁ τ₂ : Ty} {c th el : Ratchet.Expr}
    (hx : envGet? Γ x = some (.nilable σ)) (hf : falseFreeB σ = true) (ha : isAliasTy σ = false)
    (hne : x ≠ t) (hcs : capStale t (.nilable σ) (.nilable σ) = false)
    (hck : capStaleCtx t (.nilable σ) κ = false)
    (hx0 : envGet? (aliasEnv Γ x t (.nilable σ)) x = some (.nilable σ))
    (hc : SemSafeCtxA κ (andEnv Γ x t (.nilable σ) σ) (killClosOverSpine I t (.nilable σ)) c τc
      κ Γc (killClosOverSpine I t (.nilable σ)))
    (hth : SemSafeCtxA κ Γc (killClosOverSpine I t (.nilable σ)) th τ₁ κ' Γ₁ I')
    (hel : SemSafeCtxA κ (joinEnv Γc (andEnv Γ x t (.nilable σ) .nilT))
      (killClosOverSpine I t (.nilable σ)) el τ₂ κ' Γ₂ I') :
    SemSafeCtxA κ Γ I (.if' (.seq [.vasgn .lvar t (.var .lvar x),
        .if' (.var .lvar t) c (some (.var .lvar t))]) th (some el)) (joinT τ₁ τ₂) κ'
      (joinEnv Γ₁ Γ₂) I' := by
  intro m hm
  let inner : Ratchet.Expr := .if' (.var .lvar t) c (some (.var .lvar t))
  let kO : Kont := .ifK (toRuby th) (some (toRuby el))
  let kS : Kont := .seqK [toRuby inner]
  let kI : Kont := .ifK (toRuby c) (some (toRuby (.var .lvar t)))
  have hK1 : RubyCore.Proof.CatchFree [kS, kO] := by
    intro k hk
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl <;> rfl
  have hK2 : RubyCore.Proof.CatchFree [Kont.seqK [], kO] := by
    intro k hk
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl <;> rfl
  have hthJ := hth.weaken (τ := joinT τ₁ τ₂) (Γ₂ := joinEnv Γ₁ Γ₂)
    (fun _ _ hm hd => ⟨StateOk_joinEnv true hm, denM_joinT_left hd⟩)
  have helJ := hel.weaken (τ := joinT τ₁ τ₂) (Γ₂ := joinEnv Γ₁ Γ₂)
    (fun _ _ hm hd => ⟨StateOk_joinEnv false hm, denM_joinT_right hd⟩)
  -- the outer `if` on a delivered value
  have houter : ∀ (w : Value) (n : Machine), Interp.stepFn (deliverA (.val w) n [kO]) =
      .next (evalFrom n (if w.truthy then th else el)) := by
    intro w n
    simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, kO]
    cases hv : w.truthy <;> simp [Interp.withCtl, evalFrom, toRuby]
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [kO] (evalFrom m
      (.seq [.vasgn .lvar t (.var .lvar x), inner]))) from rfl)
  apply RunSpec.step (by rfl)
    (show Interp.stepFn _ = .next (pushK [kS, kO] (evalFrom m
      (.vasgn .lvar t (.var .lvar x)))) from rfl)
  apply (SemSafeCtxA.vasgnAlias hx rfl hne hcs hck m hm).bindSpec hm.rootClean hK1
  intro a n hr
  cases a with
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n [kO]) from by cases j <;> rfl)
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩
  | val v =>
    have hn : StateOk κ (aliasEnv Γ x t (.nilable σ)) (killClosOverSpine I t (.nilable σ)) n :=
      hr.2.2 v rfl
    have ht0 : envGet? (aliasEnv Γ x t (.nilable σ)) t = some (.sameAs x (.nilable σ)) :=
      envGet?_envSet_self _ _ _
    have halias : n.getLocal t = n.getLocal x := (hn.env.1 t _ ht0).2 x _ rfl
    have hv0 : denM (.nilable σ) n (n.getLocal t) := (hn.env.1 t _ ht0).1
    have henv : ∀ ρ, isAliasTy ρ = false → denM ρ n (n.getLocal t) →
        EnvOk (andEnv Γ x t (.nilable σ) ρ) n := by
      intro ρ hal hd
      have h1 := envOk_refine hn.env hx0 (by rw [← halias]; exact hd) hal
      exact envOk_refine_alias h1 (by rw [envGet?_envSet_ne _ _ _ _ hne.symm]; exact ht0) hd halias
    apply RunSpec.rebase _ hr.1
    apply RunSpec.step (by rfl)
      (show Interp.stepFn (deliverA (.val v) n [kS, kO]) =
        .next (pushK [.seqK [], kO] (evalFrom n inner)) from rfl)
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (pushK [kI, .seqK [], kO] (evalFrom n (.var .lvar t))) from rfl)
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.val (n.getLocal t)) n [kI, .seqK [], kO]) from by
        simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl, List.nil_append] using
          step_var_ctl (m := pushK [kI, .seqK [], kO] (evalFrom n (.var .lvar t))) (x := t) rfl)
    cases htr : (n.getLocal t).truthy
    · -- `x` is nil: the temporary's value falls through both `if`s to the else branch
      have hnil : denM .nilT n (n.getLocal t) := by
        rw [denM] at hv0
        rcases hv0 with hv | hv
        · simpa [denM] using hv
        · cases hg : n.getLocal t with
          | nil => simp [denM, isNilV]
          | bool b =>
            cases b
            · rw [hg] at hv; exact absurd hv (denM_not_false hf)
            · rw [hg] at htr; cases htr
          | _ => rw [hg] at htr; cases htr
      have hs : StateOk κ (joinEnv Γc (andEnv Γ x t (.nilable σ) .nilT))
          (killClosOverSpine I t (.nilable σ)) n :=
        StateOk_joinEnv false { hn with env := henv _ rfl hnil }
      apply RunSpec.step (by rfl)
        (show Interp.stepFn (deliverA (.val (n.getLocal t)) n [kI, .seqK [], kO]) =
          .next (pushK [.seqK [], kO] (evalFrom n (.var .lvar t))) from by
            simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, kI]
            simp [htr, Interp.withCtl, evalFrom, toRuby, pushK])
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.val (n.getLocal t)) n [.seqK [], kO]) from by
          simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl, List.nil_append] using
            step_var_ctl (m := pushK [.seqK [], kO] (evalFrom n (.var .lvar t))) (x := t) rfl)
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.val (n.getLocal t)) n [kO]) from rfl)
      apply RunSpec.step (by rfl) (houter _ n)
      simpa only [htr, Bool.false_eq_true, ite_false] using helJ n hs
    · have hsv : denM σ n (n.getLocal t) := by
        rw [denM] at hv0
        rcases hv0 with hv | hv
        · cases hg : n.getLocal t <;> rw [hg] at hv htr <;> simp_all [isNilV, Value.truthy]
        · exact hv
      have hs : StateOk κ (andEnv Γ x t (.nilable σ) σ) (killClosOverSpine I t (.nilable σ)) n :=
        { hn with env := henv _ ha hsv }
      apply RunSpec.step (by rfl)
        (show Interp.stepFn (deliverA (.val (n.getLocal t)) n [kI, .seqK [], kO]) =
          .next (pushK [.seqK [], kO] (evalFrom n c)) from by
            simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, kI]
            simp [htr, Interp.withCtl, evalFrom, toRuby, pushK])
      apply (hc n hs).bindSpec hn.rootClean hK2
      intro a2 n2 hr2
      cases a2 with
      | esc j =>
        apply RunSpec.step (by rfl)
          (show Interp.stepFn _ = .next (deliverA (.esc j) n2 [kO]) from by cases j <;> rfl)
        apply RunSpec.step (by rfl)
          (show Interp.stepFn _ = .next (deliverA (.esc j) n2 []) from by cases j <;> rfl)
        exact RunSpec.answer ⟨hr2.1, hr2.2.1, fun _ hv => by cases hv⟩
      | val w =>
        have hn2 := hr2.2.2 w rfl
        apply RunSpec.step (by rfl)
          (show Interp.stepFn _ = .next (deliverA (.val w) n2 [kO]) from rfl)
        apply RunSpec.step (by rfl) (houter w n2)
        apply RunSpec.rebase _ hr2.1
        cases hw : w.truthy
        · simpa only [Bool.false_eq_true, ite_false] using helJ n2 (StateOk_joinEnv true hn2)
        · simpa only [ite_true] using hthJ n2 hn2

#print axioms SemSafeCtxA.ifAndVar
end Ratchet.Denote.Typed
