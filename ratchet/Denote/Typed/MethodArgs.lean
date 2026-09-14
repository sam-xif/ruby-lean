import Denote.Typed.Primitive

/-! Arbitrary-length ordinary argument evaluation. Earlier arguments retain their declared
first-order types while later arguments run; dispatch consumes the final state index. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem denAll_append {m : Machine} {xs ys : List Ty} {vs ws : List Value}
    (hx : DenAll xs m vs) (hy : DenAll ys m ws) : DenAll (xs ++ ys) m (vs ++ ws) := by
  induction xs generalizing vs with
  | nil => cases vs <;> simp_all [DenAll]
  | cons x xs ih =>
    cases vs with
    | nil => cases hx
    | cons v vs => exact ⟨hx.1, ih hx.2⟩

theorem denAll_framed {m n : Machine} {ts : List Ty} {vs : List Value}
    (hf : ∀ τ ∈ ts, FirstOrder τ = true) (h : Framed m n) (hd : DenAll ts m vs) :
    DenAll ts n vs := by
  induction ts generalizing vs with
  | nil => cases vs <;> simp_all [DenAll]
  | cons t ts ih =>
    cases vs with
    | nil => cases hd
    | cons v vs => exact ⟨h.firstOrder t (hf t (by simp)) v hd.1,
        ih (fun t ht => hf t (by simp [ht])) hd.2⟩

theorem denAll_length {m : Machine} {ts : List Ty} {vs : List Value} (h : DenAll ts m vs) :
    vs.length = ts.length := by
  induction ts generalizing vs with
  | nil => cases vs <;> simp_all [DenAll]
  | cons t ts ih => cases vs <;> simp_all [DenAll]

theorem startArgs_cons (m : Machine) (recv : Value) (name : String) (acc : List Value)
    (e : Ratchet.Expr) (es : List Ratchet.Expr) (hp : plainArgB e = true) :
    Interp.startArgs m recv .implicit name acc (toRubyList (e :: es)) .none =
      .next (Interp.withKont m (.eval (toRuby e)) (.argsK recv .implicit name acc (toRubyList es) .none)) := by
  cases e <;> cases hp <;> rfl

/-- The continuation contract is about final argument values, not their source expressions.
It receives full conformance at the argument derivation's outgoing context. -/
theorem SemAllCtxA.startArgs {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty}
    {es : List Ratchet.Expr} {tys : List Ty} (hs : SemAllCtxA κ Γ I es tys κ' Γ' I')
    {τ : Ty} {recv : Value} {name : String} {m : Machine}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (seen : List Ty) (acc : List Value)
    (hf : ∀ σ ∈ seen ++ tys, FirstOrder σ = true) (ha : DenAll seen m acc)
    (finish : ∀ n, StateOk κ' Γ' I' n → n.kont = [] → ∀ vs, DenAll (seen ++ tys) n vs →
      StepSpec n Γ' τ (Interp.finishSend n recv .implicit name vs .none) κ' I') :
    StepSpec m Γ' τ (Interp.startArgs m recv .implicit name acc (toRubyList es) .none) κ' I' := by
  induction hs generalizing m seen acc with
  | nil => exact finish m hm hk acc (by simpa using ha)
  | @cons κ κ₁ κ₂ Γ Γ₁ Γ₂ I I₁ I₂ σ e es tys he hs hp ih =>
    rw [startArgs_cons m recv name acc e es hp]
    simp only [StepSpec, Interp.withKont, hk]
    change RunSpec m (pushK [.argsK recv .implicit name acc (toRubyList es) .none] (evalFrom m e))
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
      have hrun : RunSpec (deliverA (.val v) n [])
          (deliverA (.val v) n [.argsK recv .implicit name acc (toRubyList es) .none]) Γ₂ τ κ₂ I₂ := by
        apply RunSpec.of_stepSpec (by rfl)
        exact hnext
      exact hrun.rebase hfr
    | esc j =>
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
      exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩

#print axioms SemAllCtxA.startArgs
end Ratchet.Denote.Typed
