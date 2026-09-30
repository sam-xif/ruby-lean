import Denote.Rules.Method.MethodArgs
import Denote.Judgment.LocalFlow

/-! Argument evaluation carries mutable local facts and a saved-receiver predicate.
The final call may change caller types, so its output indices are independent of the
argument list's outgoing state. Earlier argument values retain first-order types. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

inductive SemFlowAll : Ctx → Env → Ty → LocalFacts → List Ratchet.Expr → List Ty →
    Ctx → Env → Ty → LocalFacts → Prop
  | nil {κ : Ctx} {Γ : Env} {I : Ty} {facts : LocalFacts} :
      SemFlowAll κ Γ I facts [] [] κ Γ I facts
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ : Ty}
      {f f₁ f₂ : LocalFacts} {e : Ratchet.Expr} {es : List Ratchet.Expr}
      {tys : List Ty} {current : Bool} :
      SemFlow κ Γ I f e σ current κ₁ Γ₁ I₁ f₁ →
      SemFlowAll κ₁ Γ₁ I₁ f₁ es tys κ₂ Γ₂ I₂ f₂ → plainArgB e = true →
      SemFlowAll κ Γ I f (e :: es) (σ :: tys) κ₂ Γ₂ I₂ f₂

theorem SemFlowAll.startArgsKeep {κ κ' κout : Ctx} {Γ Γ' Γout : Env} {I I' Iout : Ty}
    {facts out : LocalFacts} {es : List Ratchet.Expr} {tys : List Ty}
    (hs : SemFlowAll κ Γ I facts es tys κ' Γ' I' out)
    {τ : Ty} {recv : Value} {name : String} {m : Machine} {site : SendSite} {P : Machine → Prop}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hlocal : LocalFactsOk facts m)
    (seen : List Ty) (acc : List Value)
    (hf : ∀ σ ∈ seen ++ tys, FirstOrder σ = true) (ha : DenAll seen m acc)
    (pres : ∀ {m n}, Framed m n → P m → P n) (keep : P m)
    (finish : ∀ n, StateOk κ' Γ' I' n → n.kont = [] → LocalFactsOk out n → P n →
      ∀ vs, DenAll (seen ++ tys) n vs →
      StepSpec n Γout τ (Interp.finishSend n recv site name vs .none) κout Iout) :
    StepSpec m Γout τ (Interp.startArgs m recv site name acc (toRubyList es) .none) κout Iout := by
  induction hs generalizing m seen acc with
  | nil => exact finish m hm hk hlocal keep acc (by simpa using ha)
  | @cons κ κ₁ κ₂ Γ Γ₁ Γ₂ I I₁ I₂ σ f f₁ f₂ e es tys current he hs hp ih =>
    rw [startArgs_cons m recv name acc e es hp]
    simp only [StepSpec, Interp.withKont, hk]
    change RunSpec m (pushK [.argsK recv site name acc (toRubyList es) .none] (evalFrom m e))
      Γout τ κout Iout
    apply (he m hm hlocal).bindSpec hm.rootClean (by
      intro k h
      simp only [List.mem_singleton] at h
      subst h
      rfl)
    intro a n hn
    cases a with
    | val v =>
      have hfr : Framed m (deliverA (.val v) n []) := hn.1.1.trans (Framed_reCtl _ _ _)
      have hacc : DenAll (seen ++ [σ]) (deliverA (.val v) n []) (acc ++ [v]) :=
        denAll_append (denAll_framed (fun t ht => hf t (by simp [ht])) hfr ha)
          ⟨denM_deliverA.mpr hn.1.2.1, trivial⟩
      have hnext := ih (StateOk_deliverA (hn.1.2.2 v rfl)) rfl
        ((hn.2 v rfl).reCtl (Answer.val v).ctl []).1 (seen ++ [σ]) (acc ++ [v])
        (by simpa only [List.append_assoc, List.singleton_append] using hf) hacc (pres hfr keep)
        (by simpa only [List.append_assoc, List.singleton_append] using finish)
      have hrun : RunSpec (deliverA (.val v) n [])
          (deliverA (.val v) n [.argsK recv site name acc (toRubyList es) .none]) Γout τ κout Iout := by
        apply RunSpec.of_stepSpec (by rfl)
        exact hnext
      exact hrun.rebase hfr
    | esc j =>
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
      exact RunSpec.answer ⟨hn.1.1, hn.1.2.1, fun _ hv => by cases hv⟩

#print axioms SemFlowAll.startArgsKeep
end Ratchet.Denote.Typed
