import Denote.Judgment.Context

/-! The sequence companion contains semantic premises only. Its interpretation follows
the machine's sequence frames, including the final empty frame. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

inductive SemSeqCtxA : Ctx → Env → Ty → List Ratchet.Expr → Ty → Ctx → Env → Ty → Prop
  | last {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr} :
      SemSafeCtxA κ Γ I e τ κ' Γ' I' → SemSeqCtxA κ Γ I [e] τ κ' Γ' I'
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
      {e e' : Ratchet.Expr} {es : List Ratchet.Expr} :
      SemSafeCtxA κ Γ I e σ κ₁ Γ₁ I₁ → SemSeqCtxA κ₁ Γ₁ I₁ (e' :: es) τ κ₂ Γ₂ I₂ →
      SemSeqCtxA κ Γ I (e :: e' :: es) τ κ₂ Γ₂ I₂

inductive SemSeqA : Env → List Ratchet.Expr → Ty → Env → Prop
  | last {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty} :
      SemSafeA Γ e τ Γ' → SemSeqA Γ [e] τ Γ'
  | cons {Γ Γ₁ Γ₂ : Env} {e e' : Ratchet.Expr} {es : List Ratchet.Expr} {σ τ : Ty} :
      SemSafeA Γ e σ Γ₁ → SemSeqA Γ₁ (e' :: es) τ Γ₂ →
      SemSeqA Γ (e :: e' :: es) τ Γ₂

theorem SemSeqA.context {Γ Γ' : Env} {es : List Ratchet.Expr} {τ : Ty}
    (h : SemSeqA Γ es τ Γ') : SemSeqCtxA ctx0 Γ .ivar0 es τ ctx0 Γ' .ivar0 := by
  induction h with
  | last he => exact .last (semSafeA_iff_context.mp he)
  | cons he _ ih => exact .cons (semSafeA_iff_context.mp he) ih

private theorem seq_catchFree (es : List RubyCore.Expr) :
    RubyCore.Proof.CatchFree [.seqK es] := by
  intro k hk tag
  simp only [List.mem_singleton] at hk
  subst hk
  simp

private theorem seq_escape (es : List RubyCore.Expr) (m : Machine) (j : Jump) :
    Interp.stepFn (deliverA (.esc j) m [.seqK es]) =
      .next (deliverA (.esc j) m []) := by
  cases j <;> rfl

private theorem seq_bind {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty}
    {e : Ratchet.Expr} {σ τ : Ty}
    {es : List RubyCore.Expr} (h : SemSafeCtxA κ Γ I e σ κ₁ Γ₁ I₁) {m : Machine}
    (hm : StateOk κ Γ I m)
    (ht : ∀ n v, StateOk κ₁ Γ₁ I₁ n → denM σ n v →
      RunSpec n (deliverA (.val v) n [.seqK es]) Γ₂ τ κ₂ I₂) :
    RunSpec m (pushK [.seqK es] (evalFrom m e)) Γ₂ τ κ₂ I₂ := by
  apply (h m hm).bindSpec (seq_catchFree es)
  intro a n hr
  cases a with
  | val v => exact (ht n v (hr.2.2 v rfl) hr.2.1).rebase hr.1
  | esc j =>
    apply RunSpec.step (by rfl) (seq_escape es n j)
    exact RunSpec.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩

private theorem seq_finish {κ : Ctx} {Γ : Env} {I τ : Ty} {m : Machine} {v : Value}
    (hm : StateOk κ Γ I m) (hd : denM τ m v) :
    RunSpec m (deliverA (.val v) m [.seqK []]) Γ τ κ I := by
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next (deliverA (.val v) m []) from rfl)
  exact RunSpec.answer ⟨.refl m, hd, fun _ hv => by cases hv; exact hm⟩

theorem SemSeqCtxA.runSpec {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty} {es : List Ratchet.Expr} {τ : Ty}
    (h : SemSeqCtxA κ Γ I es τ κ' Γ' I') : ∀ m, StateOk κ Γ I m → ∀ v,
      RunSpec m (deliverA (.val v) m [.seqK (toRubyList es)]) Γ' τ κ' I' := by
  induction h with
  | @last κ κ' Γ Γ' I I' τ e he =>
    intro m hm v
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (pushK [.seqK []] (evalFrom m e)) from rfl)
    exact seq_bind he hm (fun _ _ hn hd => seq_finish hn hd)
  | @cons κ κ₁ κ₂ Γ Γ₁ Γ₂ I I₁ I₂ σ τ e e' es he ht ih =>
    intro m hm v
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ =
        .next (pushK [.seqK (toRubyList (e' :: es))] (evalFrom m e)) from rfl)
    exact seq_bind he hm (fun n v hn _ => ih n hn v)

/-- Continue a state-specific first run with a context-indexed sequence tail. -/
theorem RunSpec.thenSeq {κ₁ κ₂ : Ctx} {Γ₁ Γ₂ : Env} {I₁ I₂ σ τ : Ty}
    {m : Machine} {e e' : Ratchet.Expr} {es : List Ratchet.Expr}
    (h : RunSpec m (evalFrom m e) Γ₁ σ κ₁ I₁)
    (ht : SemSeqCtxA κ₁ Γ₁ I₁ (e' :: es) τ κ₂ Γ₂ I₂) :
    RunSpec m (evalFrom m (.seq (e :: e' :: es))) Γ₂ τ κ₂ I₂ := by
  apply RunSpec.step (by rfl)
    (show Interp.stepFn _ =
      .next (pushK [.seqK (toRubyList (e' :: es))] (evalFrom m e)) from rfl)
  apply h.bindSpec (seq_catchFree _)
  intro a n hr
  cases a with
  | val v => exact (ht.runSpec n (hr.2.2 v rfl) v).rebase hr.1
  | esc j =>
    apply RunSpec.step (by rfl) (seq_escape _ n j)
    exact RunSpec.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩

theorem SemSafeCtxA.sequence {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty}
    {es : List Ratchet.Expr} {τ : Ty} (h : SemSeqCtxA κ Γ I es τ κ' Γ' I') :
    SemSafeCtxA κ Γ I (.seq es) τ κ' Γ' I' := by
  intro m hm
  cases h with
  | @last _ _ _ _ _ _ _ e he =>
    exact RunSpec.step (by rfl) (show Interp.stepFn _ = .next (evalFrom m e) from rfl)
      (he m hm)
  | @cons _ _ _ _ Γ₁ _ _ _ _ σ _ e e' es he ht =>
    exact (he m hm).thenSeq ht

/-- Two-expression convenience form; the list theorem owns the composition proof. -/
theorem SemSafeCtxA.seq {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
    {e₁ e₂ : Ratchet.Expr} (h₁ : SemSafeCtxA κ Γ I e₁ σ κ₁ Γ₁ I₁)
    (h₂ : SemSafeCtxA κ₁ Γ₁ I₁ e₂ τ κ₂ Γ₂ I₂) :
    SemSafeCtxA κ Γ I (.seq [e₁, e₂]) τ κ₂ Γ₂ I₂ :=
  SemSafeCtxA.sequence (.cons h₁ (.last h₂))

theorem SemSeqA.runSpec {Γ Γ' : Env} {es : List Ratchet.Expr} {τ : Ty}
    (h : SemSeqA Γ es τ Γ') : ∀ m, StateOk ctx0 Γ .ivar0 m → ∀ v,
      RunSpec m (deliverA (.val v) m [.seqK (toRubyList es)]) Γ' τ := h.context.runSpec

theorem SemA.seq {Γ Γ' : Env} {es : List Ratchet.Expr} {τ : Ty}
    (h : SemSeqA Γ es τ Γ') : SemSafeA Γ (.seq es) τ Γ' :=
  semSafeA_iff_context.mpr (SemSafeCtxA.sequence h.context)

#print axioms SemSafeCtxA.sequence
#print axioms SemA.seq

theorem SemA.DJudgeSeq.last {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : SemSafeA Γ e τ Γ') : SemSeqA Γ [e] τ Γ' := .last h

theorem SemA.DJudgeSeq.cons {Γ Γ₁ Γ₂ : Env} {e e' : Ratchet.Expr}
    {es : List Ratchet.Expr} {σ τ : Ty} (h : SemSafeA Γ e σ Γ₁)
    (ht : SemSeqA Γ₁ (e' :: es) τ Γ₂) : SemSeqA Γ (e :: e' :: es) τ Γ₂ := .cons h ht

end Ratchet.Denote.Typed
