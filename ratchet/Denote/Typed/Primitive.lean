import Denote.Typed.PrimitiveBuiltin

/-! Primitive sends evaluate the receiver, then their (zero or one) argument. The list
companion keeps semantic premises and explicitly excludes argument-list syntax. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

inductive SemAllA : Env → List Ratchet.Expr → List Ty → Env → Prop
  | nil {Γ : Env} : SemAllA Γ [] [] Γ
  | cons {Γ Γ₁ Γ₂ : Env} {e : Ratchet.Expr} {es : List Ratchet.Expr} {τ : Ty} {tys : List Ty} :
      SemSafeA Γ e τ Γ₁ → SemAllA Γ₁ es tys Γ₂ → plainArgB e = true →
      SemAllA Γ (e :: es) (τ :: tys) Γ₂

theorem primitive_framed {σ τ : Ty} {name : String} {tys : List Ty} (hp : DPrim σ name tys τ)
    {m n : Machine} {v : Value} (hf : Framed m n) (hv : denM σ m v) : denM σ n v := by
  cases hp <;> simp only [denM] at hv ⊢
  all_goals first | exact hv | exact hf.nominal _ _ hv

private theorem prim_catchFree (k : Kont)
    (h : ∀ tag, k ≠ .catchK tag) : RubyCore.Proof.CatchFree [k] := by
  intro k' hk tag
  simp only [List.mem_singleton] at hk
  subst hk
  exact h tag

private theorem recv_one_step {site : SendSite} (m : Machine) (v : Value) (name : String) (e : Ratchet.Expr)
    (hp : plainArgB e = true) :
    Interp.stepFn (deliverA (.val v) m [.recvK name [toRuby e] .none site]) =
      .next (pushK [.argsK v site name [] [] .none] (evalFrom m e)) := by
  cases e <;> cases hp <;> rfl

private theorem primitive_frame {site : SendSite} {Γ : Env} {m start : Machine} {recv : Value}
    {args : List Value} {σ τ : Ty} {tys : List Ty} {name : String}
    (hp : DPrim σ name tys τ) (hm : StateOk ctx0 Γ .ivar0 m)
    (hk : m.kont = []) (hr : denM σ m recv) (ha : ArgsDen m tys args)
    (hap : answerPoint start = none)
    (hs : Interp.stepFn start = Interp.invoke m recv site name args none []) :
    RunSpec m start Γ τ := by
  apply RunSpec.of_stepSpec hap
  rw [hs]
  exact primitive_builtin hp hm hk hr ha

private theorem recv_one {site : SendSite} {Γ Γ' : Env} {m : Machine} {recv : Value}
    {e : Ratchet.Expr} {σ α τ : Ty} {name : String}
    (hp : DPrim σ name [α] τ) (he : SemSafeA Γ e α Γ') (hplain : plainArgB e = true)
    (hm : StateOk ctx0 Γ .ivar0 m) (hr : denM σ m recv) :
    RunSpec m (deliverA (.val recv) m [.recvK name [toRuby e] .none site]) Γ' τ := by
  apply RunSpec.step (by rfl) (recv_one_step m recv name e hplain)
  apply RunSpec.bind he hm (prim_catchFree _ (by intro tag; simp))
  intro a n hn
  cases a with
  | val v =>
    have hrecv := primitive_framed hp hn.1 hr
    have h := primitive_frame hp (StateOk_deliverA (hn.2.2 v rfl)) rfl
      (m := deliverA (.val v) n []) (denM_deliverA.mpr hrecv)
      (.cons (denM_deliverA.mpr hn.2.1) .nil)
      (start := deliverA (.val v) n [.argsK recv site name [] [] .none])
      (by rfl) (by rfl)
    exact h.rebase (hn.1.trans (Framed_reCtl _ _ _))
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩

private theorem recv_spec {site : SendSite} {Γ Γ' : Env} {m : Machine} {recv : Value}
    {es : List Ratchet.Expr} {σ τ : Ty} {tys : List Ty} {name : String}
    (hp : DPrim σ name tys τ) (ha : SemAllA Γ es tys Γ')
    (hm : StateOk ctx0 Γ .ivar0 m) (hr : denM σ m recv) :
    RunSpec m (deliverA (.val recv) m [.recvK name (toRubyList es) .none site]) Γ' τ := by
  have harity : tys = [] ∨ ∃ α, tys = [α] := by
    cases hp <;> simp
  rcases harity with hnil | ⟨α, hone⟩
  · subst hnil
    cases ha
    have h := primitive_frame hp (StateOk_deliverA hm) rfl
      (m := deliverA (.val recv) m []) (denM_deliverA.mpr hr) .nil
      (start := deliverA (.val recv) m [.recvK name [] .none site]) (by rfl) (by rfl)
    exact h.rebase (Framed_reCtl _ _ _)
  · subst hone
    cases ha with
    | cons he ht hplain =>
      cases ht
      exact recv_one hp he hplain hm hr

theorem SemA.prim {Γ Γ₁ Γ₂ : Env} {recv : Ratchet.Expr} {name : String}
    {args : List Ratchet.Expr} {σ τ : Ty} {tys : List Ty}
    (hr : SemSafeA Γ recv σ Γ₁) (ha : SemAllA Γ₁ args tys Γ₂) (hp : DPrim σ name tys τ) :
    SemSafeA Γ (.send (some recv) name args none) τ Γ₂ := by
  apply semSafe_of_runSpec
  intro m hm
  let site : SendSite := match toRuby recv with | .self' => .selfRecv | _ => .explicit
  apply RunSpec.step (by rfl)
    (show Interp.stepFn _ =
      .next (pushK [.recvK name (toRubyList args) .none site] (evalFrom m recv)) from ?_)
  · apply RunSpec.bind hr hm (prim_catchFree _ (by intro tag; simp))
    intro a n hn
    cases a with
    | val v => exact (recv_spec hp ha (hn.2.2 v rfl) hn.2.1).rebase hn.1
    | esc j =>
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
      exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩
  · rfl

#print axioms SemA.prim

theorem SemA.DJudgeAll.nil {Γ : Env} : SemAllA Γ [] [] Γ := .nil

theorem SemA.DJudgeAll.cons {Γ Γ₁ Γ₂ : Env} {e : Ratchet.Expr} {es : List Ratchet.Expr}
    {τ : Ty} {tys : List Ty} (h : SemSafeA Γ e τ Γ₁) (ht : SemAllA Γ₁ es tys Γ₂)
    (hp : plainArgB e = true) : SemAllA Γ (e :: es) (τ :: tys) Γ₂ := .cons h ht hp

end Ratchet.Denote.Typed
