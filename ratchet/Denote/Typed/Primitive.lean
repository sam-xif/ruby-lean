import Denote.Typed.PrimitiveBuiltin
import Denote.Typed.Context

/-! Primitive sends evaluate the receiver, then their (zero or one) argument. The list
companion keeps semantic premises and explicitly excludes argument-list syntax. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Argument evaluation threads the whole state index; dispatch uses the final context. -/
inductive SemAllCtxA : Ctx → Env → Ty → List Ratchet.Expr → List Ty → Ctx → Env → Ty → Prop
  | nil {κ : Ctx} {Γ : Env} {I : Ty} : SemAllCtxA κ Γ I [] [] κ Γ I
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ τ : Ty}
      {e : Ratchet.Expr} {es : List Ratchet.Expr} {tys : List Ty} :
      SemSafeCtxA κ Γ I e τ κ₁ Γ₁ I₁ → SemAllCtxA κ₁ Γ₁ I₁ es tys κ₂ Γ₂ I₂ →
      plainArgB e = true → SemAllCtxA κ Γ I (e :: es) (τ :: tys) κ₂ Γ₂ I₂

inductive SemAllA : Env → List Ratchet.Expr → List Ty → Env → Prop
  | nil {Γ : Env} : SemAllA Γ [] [] Γ
  | cons {Γ Γ₁ Γ₂ : Env} {e : Ratchet.Expr} {es : List Ratchet.Expr} {τ : Ty} {tys : List Ty} :
      SemSafeA Γ e τ Γ₁ → SemAllA Γ₁ es tys Γ₂ → plainArgB e = true →
      SemAllA Γ (e :: es) (τ :: tys) Γ₂

theorem SemAllA.context {Γ Γ' : Env} {es : List Ratchet.Expr} {tys : List Ty}
    (h : SemAllA Γ es tys Γ') : SemAllCtxA ctx0 Γ .ivar0 es tys ctx0 Γ' .ivar0 := by
  induction h with
  | nil => exact .nil
  | cons he _ hp ih => exact .cons (semSafeA_iff_context.mp he) ih hp

theorem primitive_framed {σ τ : Ty} {name : String} {tys : List Ty} (hp : DPrim σ name tys τ)
    {m n : Machine} {v : Value} (hf : Framed m n) (hv : denM σ m v) : denM σ n v := by
  cases hp with
  | arrayIndex hfo => exact hf.firstOrder (.arrayOf _) hfo _ hv
  | hashIndex hfo => exact hf.firstOrder (.hashOf _ _) hfo _ hv
  | _ =>
    simp only [denM] at hv ⊢
    first | exact hv | exact hf.nominal _ _ hv

theorem prim_catchFree (k : Kont)
    (h : ∀ tag, k ≠ .catchK tag) : RubyCore.Proof.CatchFree [k] := by
  intro k' hk tag
  simp only [List.mem_singleton] at hk
  subst hk
  exact h tag

theorem recv_one_step {site : SendSite} (m : Machine) (v : Value) (name : String) (e : Ratchet.Expr)
    (hp : plainArgB e = true) :
    Interp.stepFn (deliverA (.val v) m [.recvK name [toRuby e] .none site]) =
      .next (pushK [.argsK v site name [] [] .none] (evalFrom m e)) := by
  cases e <;> cases hp <;> rfl

theorem primitive_frame {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env}
    {m start : Machine} {recv : Value}
    {args : List Value} {σ τ : Ty} {tys : List Ty} {name : String}
    (hp : DPrim σ name tys τ) (hm : StateOk κ Γ I m)
    (hk : m.kont = []) (hr : denM σ m recv) (ha : ArgsDen m tys args)
    (hap : answerPoint start = none)
    (hs : Interp.stepFn start = Interp.invoke m recv site name args none [])
    (hfree : nameFreeN κ name = true)
    (hstring : σ = .cls "String" →
      isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    RunSpec m start Γ τ κ I := by
  apply RunSpec.of_stepSpec hap
  rw [hs]
  exact primitive_builtin hp hm hk hr ha hfree hstring

private theorem recv_one {κ κ' : Ctx} {I I' : Ty} {site : SendSite} {Γ Γ' : Env}
    {m : Machine} {recv : Value}
    {e : Ratchet.Expr} {σ α τ : Ty} {name : String}
    (hp : DPrim σ name [α] τ) (he : SemSafeCtxA κ Γ I e α κ' Γ' I')
    (hplain : plainArgB e = true) (hm : StateOk κ Γ I m) (hr : denM σ m recv)
    (hfree : nameFreeN κ' name = true)
    (hstring : σ = .cls "String" →
      isANoOk κ'.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    RunSpec m (deliverA (.val recv) m [.recvK name [toRuby e] .none site]) Γ' τ κ' I' := by
  apply RunSpec.step (by rfl) (recv_one_step m recv name e hplain)
  apply (he m hm).bindSpec (prim_catchFree _ (by intro tag; simp))
  intro a n hn
  cases a with
  | val v =>
    have hrecv := primitive_framed hp hn.1 hr
    have h := primitive_frame hp (StateOk_deliverA (hn.2.2 v rfl)) rfl
      (m := deliverA (.val v) n []) (denM_deliverA.mpr hrecv)
      (.cons (denM_deliverA.mpr hn.2.1) .nil)
      (start := deliverA (.val v) n [.argsK recv site name [] [] .none])
      (by rfl) (by rfl) hfree hstring
    exact h.rebase (hn.1.trans (Framed_reCtl _ _ _))
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩

private theorem recv_spec {κ κ' : Ctx} {I I' : Ty} {site : SendSite} {Γ Γ' : Env}
    {m : Machine} {recv : Value}
    {es : List Ratchet.Expr} {σ τ : Ty} {tys : List Ty} {name : String}
    (hp : DPrim σ name tys τ) (ha : SemAllCtxA κ Γ I es tys κ' Γ' I')
    (hm : StateOk κ Γ I m) (hr : denM σ m recv)
    (hfree : nameFreeN κ' name = true)
    (hstring : σ = .cls "String" →
      isANoOk κ'.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    RunSpec m (deliverA (.val recv) m [.recvK name (toRubyList es) .none site]) Γ' τ κ' I' := by
  have harity : tys = [] ∨ ∃ α, tys = [α] := by
    cases hp <;> simp
  rcases harity with hnil | ⟨α, hone⟩
  · subst hnil
    cases ha
    have h := primitive_frame hp (StateOk_deliverA hm) rfl
      (m := deliverA (.val recv) m []) (denM_deliverA.mpr hr) .nil
      (start := deliverA (.val recv) m [.recvK name [] .none site]) (by rfl) (by rfl) hfree hstring
    exact h.rebase (Framed_reCtl _ _ _)
  · subst hone
    cases ha with
    | cons he ht hplain =>
      cases ht
      exact recv_one hp he hplain hm hr hfree hstring

theorem SemSafeCtxA.prim {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty}
    {recv : Ratchet.Expr} {name : String}
    {args : List Ratchet.Expr} {σ τ : Ty} {tys : List Ty}
    (hr : SemSafeCtxA κ Γ I recv σ κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args tys κ₂ Γ₂ I₂) (hp : DPrim σ name tys τ)
    (hfree : nameFreeN κ₂ name = true)
    (hstring : σ = .cls "String" →
      isANoOk κ₂.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    SemSafeCtxA κ Γ I (.send (some recv) name args none) τ κ₂ Γ₂ I₂ := by
  intro m hm
  let site : SendSite := match toRuby recv with | .self' => .selfRecv | _ => .explicit
  apply RunSpec.step (by rfl)
    (show Interp.stepFn _ =
      .next (pushK [.recvK name (toRubyList args) .none site] (evalFrom m recv)) from ?_)
  · apply (hr m hm).bindSpec (prim_catchFree _ (by intro tag; simp))
    intro a n hn
    cases a with
    | val v => exact (recv_spec hp ha (hn.2.2 v rfl) hn.2.1 hfree hstring).rebase hn.1
    | esc j =>
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
      exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩
  · rfl

theorem SemA.prim {Γ Γ₁ Γ₂ : Env} {recv : Ratchet.Expr} {name : String}
    {args : List Ratchet.Expr} {σ τ : Ty} {tys : List Ty}
    (hr : SemSafeA Γ recv σ Γ₁) (ha : SemAllA Γ₁ args tys Γ₂) (hp : DPrim σ name tys τ) :
    SemSafeA Γ (.send (some recv) name args none) τ Γ₂ :=
  semSafeA_iff_context.mpr
    ((semSafeA_iff_context.mp hr).prim ha.context hp (by rfl) (by intro; rfl))

#print axioms SemSafeCtxA.prim
#print axioms SemA.prim

theorem SemA.DJudgeAll.nil {Γ : Env} : SemAllA Γ [] [] Γ := .nil

theorem SemA.DJudgeAll.cons {Γ Γ₁ Γ₂ : Env} {e : Ratchet.Expr} {es : List Ratchet.Expr}
    {τ : Ty} {tys : List Ty} (h : SemSafeA Γ e τ Γ₁) (ht : SemAllA Γ₁ es tys Γ₂)
    (hp : plainArgB e = true) : SemAllA Γ (e :: es) (τ :: tys) Γ₂ := .cons h ht hp

end Ratchet.Denote.Typed
