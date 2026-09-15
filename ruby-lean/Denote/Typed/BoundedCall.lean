import Denote.Typed.BoundedMethod
import Denote.Typed.MethodArgs

/-! Bounded argument evaluation and the guarded call rule. A body contract at N suffices
for a call at N+1; the actual send step, not an assumption about argument values, pays for it. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

inductive SemAllCtxAt (N : Nat) : Ctx → Env → Ty → List Ratchet.Expr → List Ty → Ctx → Env → Ty → Prop
  | nil {κ : Ctx} {Γ : Env} {I : Ty} : SemAllCtxAt N κ Γ I [] [] κ Γ I
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ τ : Ty}
      {e : Ratchet.Expr} {es : List Ratchet.Expr} {tys : List Ty} :
      SemSafeCtxAt N κ Γ I e τ κ₁ Γ₁ I₁ → SemAllCtxAt N κ₁ Γ₁ I₁ es tys κ₂ Γ₂ I₂ →
      plainArgB e = true → SemAllCtxAt N κ Γ I (e :: es) (τ :: tys) κ₂ Γ₂ I₂

theorem SemAllCtxAt.mono {N n : Nat} {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty}
    {es : List Ratchet.Expr} {tys : List Ty}
    (h : SemAllCtxAt N κ Γ I es tys κ' Γ' I') (hn : n ≤ N) :
    SemAllCtxAt n κ Γ I es tys κ' Γ' I' := by
  induction h with
  | nil => exact .nil
  | cons he _ hp ih => exact .cons (he.mono hn) ih hp

/-- The continuation contract is about final argument values, not their source expressions.
It receives full conformance at the argument derivation's outgoing context. -/
theorem SemAllCtxAt.startArgs {N : Nat} {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty}
    {es : List Ratchet.Expr} {tys : List Ty} (hs : SemAllCtxAt N κ Γ I es tys κ' Γ' I')
    {τ : Ty} {recv : Value} {name : String} {m : Machine}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (seen : List Ty) (acc : List Value)
    (hf : ∀ σ ∈ seen ++ tys, FirstOrder σ = true) (ha : DenAll seen m acc)
    (finish : ∀ n, StateOk κ' Γ' I' n → n.kont = [] → ∀ vs, DenAll (seen ++ tys) n vs →
      StepSpecAt N n Γ' τ (Interp.finishSend n recv .implicit name vs .none) κ' I') :
    StepSpecAt N m Γ' τ (Interp.startArgs m recv .implicit name acc (toRubyList es) .none) κ' I' := by
  induction hs generalizing m seen acc with
  | nil => exact finish m hm hk acc (by simpa using ha)
  | @cons κ κ₁ κ₂ Γ Γ₁ Γ₂ I I₁ I₂ σ e es tys he hs hp ih =>
    rw [startArgs_cons m recv name acc e es hp]
    simp only [StepSpecAt, Interp.withKont, hk]
    change RunSpecAt N m (pushK [.argsK recv .implicit name acc (toRubyList es) .none] (evalFrom m e))
      Γ₂ τ κ₂ I₂
    apply (he m hm).bindSpec (by
      intro k h tag
      simp only [List.mem_singleton] at h
      subst h
      simp)
    intro a n hn
    cases a with
    | val v =>
      have hfr : Framed m (deliverA (.val v) n []) := hn.1.trans (Framed_reCtl _ _ _)
      have hacc : DenAll (seen ++ [σ]) (deliverA (.val v) n []) (acc ++ [v]) :=
        denAll_append (denAll_framed (fun t ht => hf t (by simp [ht])) hfr ha)
          ⟨denM_deliverA.mpr hn.2.1, trivial⟩
      have hnext := ih (StateOk_deliverA (hn.2.2 v rfl)) rfl (seen ++ [σ]) (acc ++ [v])
        (by simpa only [List.append_assoc, List.singleton_append] using hf) hacc
        (by simpa only [List.append_assoc, List.singleton_append] using finish)
      have hrun : RunSpecAt N (deliverA (.val v) n [])
          (deliverA (.val v) n [.argsK recv .implicit name acc (toRubyList es) .none]) Γ₂ τ κ₂ I₂ := by
        apply RunSpecAt.of_stepSpecWithin (by rfl)
        exact hnext
      exact hrun.rebase hfr
    | esc j =>
      apply RunSpecAt.of_stepSpecWithin (by rfl)
      have hs : Interp.stepFn (deliverA (.esc j) n [.argsK recv .implicit name acc (toRubyList es) .none]) =
          .next (deliverA (.esc j) n []) := by cases j <;> rfl
      rw [hs]
      exact RunSpecAt.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩


theorem SemSafeCtxAt.callSig {N : Nat} {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' τ : Ty}
    {decl : Defn} {ps : List SigParam} {args : List Ratchet.Expr}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hbody : SemSafeCtxAt N (κ'.withFrame (some ⟨"Object", "Object", decl.name⟩)) ps I' decl.body τ
      (κ'.withFrame (some ⟨"Object", "Object", decl.name⟩)) Γb I')
    (hargs : SemAllCtxAt N κ Γ I args (ps.map (·.2)) κ' Γ' I')
    (hd : decl ∈ κ'.defs)
    (hstart : κ.scope.runtimeMain = true) (hruntime : κ'.scope.runtimeMain = true)
    (hself : κ'.selfTy = none) (hblock : κ'.blockTy = none) (hconst : κ'.consts = [])
    (hasms : κ'.asms = []) (hI : FirstOrder I' = true)
    (hΓ : ∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxAt (N + 1) κ Γ I (.send none decl.name args none) τ κ' Γ' I' := by
  intro m hm
  let start := evalFrom m (.send none decl.name args none)
  have hfinish (n : Machine) (hn : StateOk κ' Γ' I' n) (hk : n.kont = [])
      (vs : List Value) (hv : DenAll (ps.map (·.2)) n vs) :
      StepSpecAt N n Γ' τ (Interp.finishSend n (.ref Boot.mainId) .implicit decl.name vs .none) κ' I' := by
    obtain ⟨next, hs, hr⟩ := top_method_runSpecAt hparams hps hτ hbody hn hd
      (ReframeFO.empty hI hself hblock hconst) hasms hconst hΓ hk
      (by simpa using denAll_length hv) hv hruntime hblock
    rw [(hn.runtime hruntime).self] at hs
    rw [hs]
    exact hr
  apply RunSpecAt.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpecAt.of_stepSpec (by rfl)
  have hh := hargs.startArgs (m := start) (recv := .ref Boot.mainId) (name := decl.name)
    (StateOk_reCtl hm _ []) rfl [] []
    (by
      intro σ hσ
      simp only [List.nil_append, List.mem_map] at hσ
      obtain ⟨p, hp, rfl⟩ := hσ
      exact (hps p hp).1)
    trivial hfinish
  have hselfm : start.currentFrame.self = .ref Boot.mainId := (hm.runtime hstart).self
  change StepSpecAt N start Γ' τ
    (Interp.startArgs start start.currentFrame.self .implicit decl.name [] (toRubyList args) .none) κ' I'
  rw [hselfm]
  exact hh


#print axioms SemAllCtxAt.startArgs
#print axioms SemSafeCtxAt.callSig
end Ratchet.Denote.Typed
