import Books.TypeSoundness.Rules.Expr.CaseEq

/-! `C === x` on a plain local (string interpolation's `String === t`), and `dead`: code
behind a `never`-typed local, which no conformant machine reaches. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem SemSafeCtxA.ifCaseEqVar {κ κ' : Ctx} {Γ Γ₁ Γ₂ : Env} {I I' : Ty} {x cn : String}
    {ρ τ₁ τ₂ : Ty} {th el : Checker.Expr}
    (hx : envGet? Γ x = some ρ) (hg : ifIsAB κ ρ cn = true)
    (hfree3 : nameFreeN κ "===" = true)
    (hth : SemSafeCtxA κ (envSet Γ x (isATy κ.classes κ.wholeCls cn ρ)) I th τ₁ κ' Γ₁ I')
    (hel : SemSafeCtxA κ (envSet Γ x (notATy κ.classes κ.wholeCls cn ρ)) I el τ₂ κ' Γ₂ I') :
    SemSafeCtxA κ Γ I (.if' (.send (some (.const cn)) "===" [.var .lvar x] none) th (some el))
      (joinT τ₁ τ₂) κ' (joinEnv Γ₁ Γ₂) I' := by
  simp only [ifIsAB, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hrecv, hcls⟩, hcf⟩, hbound⟩, hfree⟩, hTfo⟩, hTal⟩, hFfo⟩, hFal⟩ := hg
  intro m hm
  let k : Kont := .ifK (toRuby th) (some (toRuby el))
  obtain ⟨c, hnamed, hlex⟩ := isA_class_named hm hcf hcls
  have hρ : stripAlias ρ = ρ := by
    cases ρ <;> simp_all [stripAlias, isARecvB, isALeafB]
  have hv0 : denM ρ m (m.getLocal x) := by
    have := (hm.env.1 x _ hx).1
    rwa [hρ] at this
  obtain ⟨_, hT, hF⟩ := recv_facts hm hcf hbound hfree hnamed ρ _ hrecv hv0
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m
      (.send (some (.const cn)) "===" [.var .lvar x] none))) from rfl)
  apply (caseEq_cond hm hnamed hlex hfree3).bindSpec hm.rootClean
    (by intro c hc; simp at hc; subst hc; rfl)
  intro a n hr
  cases a with
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hr.1.1, hr.1.2.1, fun _ hv => by cases hv⟩
  | val w =>
    obtain ⟨hw, c', ks', hre⟩ := hr.2 w rfl
    subst hw
    have hloc : n.getLocal x = m.getLocal x := by rw [hre]; exact getLocal_reCtl m _ _ x
    have hn : StateOk κ Γ I n := hr.1.2.2 _ rfl
    have hbranch : Interp.stepFn (deliverA (.val (.bool (isA m.heap (m.getLocal x) c))) n [k]) =
        .next (evalFrom n (if isA m.heap (m.getLocal x) c then th else el)) := by
      simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, k]
      cases hb' : isA m.heap (m.getLocal x) c <;> simp [Value.truthy, Interp.withCtl, evalFrom]
    apply RunSpec.step (by rfl) hbranch
    apply RunSpec.rebase _ hr.1.1
    cases hb' : isA m.heap (m.getLocal x) c
    · have hs : StateOk κ _ I n :=
        { hn with env := (envOk_refine hn.env hx
            (by rw [hloc]; exact hr.1.1.firstOrder _ hFfo _ (hF hb')) hFal) }
      simpa only [Bool.false_eq_true, ite_false] using
        (hel.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv false hm, denM_joinT_right hd⟩)) n hs
    · have hs : StateOk κ _ I n :=
        { hn with env := (envOk_refine hn.env hx
            (by rw [hloc]; exact hr.1.1.firstOrder _ hTfo _ (hT hb')) hTal) }
      simpa only [ite_true] using
        (hth.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv true hm, denM_joinT_left hd⟩)) n hs

theorem SemSafeCtxA.dead {κ : Ctx} {Γ : Env} {I τ : Ty} {x : String} {e : Checker.Expr}
    (hx : envGet? Γ x = some τ) (hn : stripAlias τ = .never) (_hp : plainArgB e = true) :
    SemSafeCtxA κ Γ I e .never κ Γ I := by
  intro m hm
  have h := (hm.env.1 x _ hx).1
  rw [hn] at h
  exact absurd h (by simp [denM])

theorem SemSafeCtxA.widen {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Checker.Expr} (σ : Ty)
    (h : SemSafeCtxA κ Γ I e τ κ' Γ' I') : SemSafeCtxA κ Γ I e (joinT τ σ) κ' Γ' I' :=
  h.weaken (fun _ _ hm hd => ⟨hm, denM_joinT_left hd⟩)

#print axioms SemSafeCtxA.ifCaseEqVar
#print axioms SemSafeCtxA.widen
#print axioms SemSafeCtxA.dead
end Checker.Soundness.Typed
