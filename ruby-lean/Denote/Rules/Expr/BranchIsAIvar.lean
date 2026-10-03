import Denote.Rules.Expr.BranchIsA
import Denote.Rules.Instance.InstanceWrite
import Denote.Ty.JoinInv

/-! `is_a?` narrowing of an instance variable. The branch sees the field at the refined
type; the incoming spine is restored afterwards because a refinement only shrinks a type. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem isATy_sub (C W : CTable) (cn : String) :
    ∀ (ρ : Ty) (m : Machine) (v : Value), denM (isATy C W cn ρ) m v → denM ρ m v := by
  intro ρ
  induction ρ with
  | union σ τ ihσ ihτ =>
    intro m v h
    simp only [isATy] at h
    rcases denM_joinT_inv h with h | h
    · simp only [denM]; exact .inl (ihσ m v h)
    · simp only [denM]; exact .inr (ihτ m v h)
  | nilable ρ ih =>
    intro m v h
    simp only [isATy] at h
    rcases denM_joinT_inv h with h | h
    · simp only [isANilPart] at h
      simp only [denM]
      split at h
      · exact .inl (by simpa [denM] using h)
      · split at h
        · simp [denM] at h
        · exact .inl (by simpa [denM] using h)
    · simp only [denM]; exact .inr (ih m v h)
  | _ =>
    intro m v h
    simp only [isATy] at h
    split at h
    · simp [denM] at h
    · exact h

theorem notATy_sub (C W : CTable) (cn : String) :
    ∀ (ρ : Ty) (m : Machine) (v : Value), denM (notATy C W cn ρ) m v → denM ρ m v := by
  intro ρ
  induction ρ with
  | union σ τ ihσ ihτ =>
    intro m v h
    simp only [notATy] at h
    rcases denM_joinT_inv h with h | h
    · simp only [denM]; exact .inl (ihσ m v h)
    · simp only [denM]; exact .inr (ihτ m v h)
  | nilable ρ ih =>
    intro m v h
    simp only [notATy] at h
    rcases denM_joinT_inv h with h | h
    · simp only [notANilPart] at h
      simp only [denM]
      split at h
      · simp [denM] at h
      · exact .inl (by simpa [denM] using h)
    · simp only [denM]; exact .inr (ih m v h)
  | _ =>
    intro m v h
    simp only [notATy] at h
    split at h
    · simp [denM] at h
    · exact h

/-- Replace a field's type by one its current value has. -/
theorem selfSpine_refine {m : Machine} {I σ : Ty} {x : String} {closed : Bool}
    (hi : SelfSpineOk I m closed)
    (hv : denM σ m (ivarOf m.heap m.currentFrame.self x)) :
    SelfSpineOk (ivarSet I x σ) m closed := by
  have hshape := denSpineFrom_shape hi.1
  refine ⟨denSpineFrom_of_get hshape.set ?_, ?_⟩
  · intro y τ _ hg
    rw [ivarGet?_set hshape] at hg
    by_cases hy : y = x
    · simp only [hy, ↓reduceIte] at hg ⊢
      cases Option.some.inj hg; exact hv
    · simp only [hy, ↓reduceIte] at hg
      exact denSpineFrom_get hi.1 (by simp) hg
  · intro y hg hc
    rw [ivarGet?_set hshape] at hg
    by_cases hy : y = x
    · simp [hy] at hg
    · simp only [hy, ↓reduceIte] at hg
      exact hi.2 y hg hc

/-- Forget a refinement: the refined type's values are values of the declared one. -/
theorem selfSpine_unrefine {m : Machine} {I ρ σ : Ty} {x : String} {closed : Bool}
    (hshape : SpineShape I) (hx : ivarGet? I x = some ρ)
    (hi : SelfSpineOk (ivarSet I x σ) m closed)
    (hsub : ∀ v, denM σ m v → denM ρ m v) : SelfSpineOk I m closed := by
  refine ⟨denSpineFrom_of_get hshape ?_, ?_⟩
  · intro y τ _ hg
    by_cases hy : y = x
    · subst hy
      rw [hx] at hg; cases hg
      exact hsub _ (denSpineFrom_get hi.1 (by simp) (by rw [ivarGet?_set hshape]; simp))
    · exact denSpineFrom_get hi.1 (by simp) (by rw [ivarGet?_set hshape]; simpa [hy] using hg)
  · intro y hg hc
    have hy : y ≠ x := by rintro rfl; rw [hx] at hg; cases hg
    exact hi.2 y (by rw [ivarGet?_set hshape]; simpa [hy] using hg) hc

theorem stepFn_ivarRead_push (m : Machine) (x : String) (K : List Kont) :
    Interp.stepFn (pushK K (evalFrom m (.var .ivar x))) =
      .next (deliverA (.val (ivarOf m.heap m.currentFrame.self x)) m K) := by
  change (match m.currentFrame.self with
    | .ref o => StepResult.next (deliverA (.val
        (((m.heap.get o).ivars.find? (fun p : String × Value => p.1 == x)).map
          (fun p : String × Value => p.2) |>.getD .nil)) m K)
    | _ => StepResult.next (deliverA (.val .nil) m K)) = _
  cases m.currentFrame.self <;> simp only [ivarOf] <;> try rfl
  rename_i o
  cases (m.heap.get o).ivars.find? (·.1 == x) <;> rfl

theorem SemSafeCtxA.ifIsAIvar {κ κ' : Ctx} {Γ Γ₁ Γ₂ : Env} {I : Ty} {x cn : String}
    {ρ τ₁ τ₂ : Ty} {t e : Ratchet.Expr}
    (hx : ivarGet? I x = some ρ) (hg : ifIsAB κ ρ cn = true)
    (ht : SemSafeCtxA κ Γ (ivarSet I x (isATy κ.classes κ.wholeCls cn ρ)) t τ₁ κ' Γ₁
      (ivarSet I x (isATy κ.classes κ.wholeCls cn ρ)))
    (he : SemSafeCtxA κ Γ (ivarSet I x (notATy κ.classes κ.wholeCls cn ρ)) e τ₂ κ' Γ₂
      (ivarSet I x (notATy κ.classes κ.wholeCls cn ρ))) :
    SemSafeCtxA κ Γ I (.if' (.send (some (.var .ivar x)) "is_a?" [.const cn] none) t (some e))
      (joinT τ₁ τ₂) κ' (joinEnv Γ₁ Γ₂) I := by
  simp only [ifIsAB, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hrecv, hcls⟩, hcf⟩, hbound⟩, hfree⟩, hTfo⟩, _⟩, hFfo⟩, _⟩ := hg
  intro m hm
  let k : Kont := .ifK (toRuby t) (some (toRuby e))
  let vx := ivarOf m.heap m.currentFrame.self x
  obtain ⟨c, hnamed, hlex⟩ := isA_class_named hm hcf hcls
  have hshape := denSpineFrom_shape hm.selfSpine.1
  have hv0 : denM ρ m vx := denSpineFrom_get hm.selfSpine.1 (by simp) hx
  obtain ⟨_, hT, hF⟩ := recv_facts hm hcf hbound hfree hnamed ρ _ hrecv hv0
  have hM : StateOk κ Γ I (deliverA (.val (.ref c)) m []) := StateOk_deliverA hm
  obtain ⟨hdisp, _, _⟩ := recv_facts hM hcf hbound hfree (cn := cn) (k := c) hnamed ρ _ hrecv
    (denM_deliverA.mpr hv0)
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m
      (.send (some (.var .ivar x)) "is_a?" [.const cn] none))) from rfl)
  apply (isA_cond hm hnamed hlex rfl (stepFn_ivarRead_push m x _) hdisp).bindSpec hm.rootClean
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
    have hloc : ivarOf n.heap n.currentFrame.self x = vx := by rw [hre]; rfl
    have hn : StateOk κ Γ I n := hr.1.2.2 _ rfl
    have hbranch : Interp.stepFn (deliverA (.val (.bool (isA m.heap vx c))) n [k]) =
        .next (evalFrom n (if isA m.heap vx c then t else e)) := by
      simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, k]
      cases hb' : isA m.heap vx c <;> simp [Value.truthy, Interp.withCtl, evalFrom]
    apply RunSpec.step (by rfl) hbranch
    apply RunSpec.rebase _ hr.1.1
    cases hb' : isA m.heap vx c
    · have hd : denM (notATy κ.classes κ.wholeCls cn ρ) n
          (ivarOf n.heap n.currentFrame.self x) := by
        rw [hloc]; exact hr.1.1.firstOrder _ hFfo _ (hF hb')
      have hs : StateOk κ Γ (ivarSet I x (notATy κ.classes κ.wholeCls cn ρ)) n :=
        { hn with selfSpine := selfSpine_refine hn.selfSpine hd }
      simpa only [Bool.false_eq_true, ite_false] using
        (he.weaken (fun m' _ hm' hd' =>
          ⟨{ StateOk_joinEnv false hm' with
              selfSpine := selfSpine_unrefine hshape hx hm'.selfSpine
                (notATy_sub _ _ _ ρ m') },
            denM_joinT_right hd'⟩)) n hs
    · have hd : denM (isATy κ.classes κ.wholeCls cn ρ) n
          (ivarOf n.heap n.currentFrame.self x) := by
        rw [hloc]; exact hr.1.1.firstOrder _ hTfo _ (hT hb')
      have hs : StateOk κ Γ (ivarSet I x (isATy κ.classes κ.wholeCls cn ρ)) n :=
        { hn with selfSpine := selfSpine_refine hn.selfSpine hd }
      simpa only [ite_true] using
        (ht.weaken (fun m' _ hm' hd' =>
          ⟨{ StateOk_joinEnv true hm' with
              selfSpine := selfSpine_unrefine hshape hx hm'.selfSpine
                (isATy_sub _ _ _ ρ m') },
            denM_joinT_left hd'⟩)) n hs

#print axioms SemSafeCtxA.ifIsAIvar
end Ratchet.Denote.Typed
