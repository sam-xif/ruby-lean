import Books.TypeSoundness.Rules.Primitive.Primitive
import Books.TypeSoundness.Denotation.Join

/-! Array literals evaluate left to right, retaining first-order element denotations. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem stepSpec_array {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {τ : Ty}
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (xs : List Value) (hd : ∀ x ∈ xs, denM τ m x) :
    StepSpec m Γ (.arrayOf τ) (Interp.continueArray m xs []) κ I := by
  have h := RunSpec.answer (array_alloc_result hm xs hd)
  simpa only [StepSpec, Interp.continueArray, Builtins.allocArr, Heap.alloc,
    Interp.withCtl, deliverA, Answer.ctl, hk] using h

private theorem continueArray_cons (m : Machine) (acc : List Value)
    (e : Checker.Expr) (es : List Checker.Expr) (hp : plainArgB e = true) :
    Interp.continueArray m acc (toRubyList (e :: es)) =
      .next (Interp.withKont m (.eval (toRuby e)) (.arrK acc (toRubyList es))) := by
  cases e <;> cases hp <;> rfl

private theorem array_spec {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty}
    {es : List Checker.Expr} {tys : List Ty}
    (hs : SemAllCtxA κ Γ I es tys κ' Γ' I') {τ : Ty} (hf : FirstOrder τ = true)
    (ht : ∀ σ ∈ tys, ∀ m v, denM σ m v → denM τ m v)
    {m : Machine} (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (acc : List Value) (ha : ∀ v ∈ acc, denM τ m v) :
    StepSpec m Γ' (.arrayOf τ) (Interp.continueArray m acc (toRubyList es)) κ' I' := by
  induction hs generalizing m acc with
  | nil => exact stepSpec_array hm hk acc ha
  | @cons κ κ₁ κ₂ Γ Γ₁ Γ₂ I I₁ I₂ σ e es tys he hs hp ih =>
    rw [continueArray_cons m acc e es hp]
    simp only [StepSpec, Interp.withKont, hk]
    change RunSpec m (pushK [.arrK acc (toRubyList es)] (evalFrom m e)) Γ₂ (.arrayOf τ) κ₂ I₂
    apply (he m hm).bindSpec hm.rootClean (by
      intro k h
      simp only [List.mem_singleton] at h
      subst h
      rfl)
    intro a n hn
    cases a with
    | val v =>
      have hacc : ∀ w ∈ acc ++ [v], denM τ (deliverA (.val v) n []) w := by
        intro w hw
        apply denM_deliverA.mpr
        rcases List.mem_append.mp hw with hw | hw
        · exact hn.1.firstOrder τ hf w (ha w hw)
        · have hw : w = v := List.mem_singleton.mp hw
          subst w
          exact ht σ (by simp) n v hn.2.1
      have hnext := ih (fun σ hσ => ht σ (by simp [hσ]))
        (StateOk_deliverA (hn.2.2 v rfl)) rfl (acc ++ [v]) hacc
      have h : RunSpec (deliverA (.val v) n [])
          (deliverA (.val v) n [.arrK acc (toRubyList es)]) Γ₂ (.arrayOf τ) κ₂ I₂ := by
        apply RunSpec.of_stepSpec (by rfl)
        exact hnext
      exact h.rebase (hn.1.trans (Framed_reCtl _ _ _))
    | esc j =>
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
      exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩

theorem denM_elemTy {tys : List Ty} {σ : Ty} (hσ : σ ∈ tys)
    {m : Machine} {v : Value} (hv : denM σ m v) : denM (elemTy tys) m v := by
  induction tys with
  | nil => cases hσ
  | cons t ts ih =>
    rcases List.mem_cons.mp hσ with h | h
    · subst σ; exact denM_joinT_left hv
    · exact denM_joinT_right (ih h)

theorem SemSafeCtxA.arrayLit {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty}
    {es : List Checker.Expr} {tys : List Ty}
    (hs : SemAllCtxA κ Γ I es tys κ' Γ' I') (hf : FirstOrder (elemTy tys) = true) :
    SemSafeCtxA κ Γ I (.array es) (.arrayOf (elemTy tys)) κ' Γ' I' := by
  intro m hm
  apply RunSpec.rebase (middle := evalFrom m (.array es)) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  exact array_spec hs hf (fun _ ht _ _ hv => denM_elemTy ht hv)
    (StateOk_reCtl hm _ []) rfl [] (by simp)

theorem SemA.arrayLit {Γ Γ' : Env} {es : List Checker.Expr} {tys : List Ty}
    (hs : SemAllA Γ es tys Γ') (hf : FirstOrder (elemTy tys) = true) :
    SemSafeA Γ (.array es) (.arrayOf (elemTy tys)) Γ' :=
  semSafeA_iff_context.mpr (SemSafeCtxA.arrayLit hs.context hf)

#print axioms SemSafeCtxA.arrayLit
#print axioms SemA.arrayLit
end Checker.Soundness.Typed
