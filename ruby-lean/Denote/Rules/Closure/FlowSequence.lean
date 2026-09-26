import Denote.Judgment.LocalFlow

/-! Sequences thread value types, contexts and mutable local facts together. The
continuation receives the previous expression's proved facts at its actual answer. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

inductive SemFlowSeq : Ctx → Env → Ty → LocalFacts → List Ratchet.Expr → Ty → Bool →
    Ctx → Env → Ty → LocalFacts → Prop
  | last {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {facts out : LocalFacts}
      {e : Ratchet.Expr} {current : Bool} :
      SemFlow κ Γ I facts e τ current κ' Γ' I' out →
      SemFlowSeq κ Γ I facts [e] τ current κ' Γ' I' out
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty} {f f₁ f₂ : LocalFacts}
      {e e' : Ratchet.Expr} {es : List Ratchet.Expr} {c c' : Bool} :
      SemFlow κ Γ I f e σ c κ₁ Γ₁ I₁ f₁ →
      SemFlowSeq κ₁ Γ₁ I₁ f₁ (e' :: es) τ c' κ₂ Γ₂ I₂ f₂ →
      SemFlowSeq κ Γ I f (e :: e' :: es) τ c' κ₂ Γ₂ I₂ f₂

private theorem seq_catchFree (es : List RubyCore.Expr) : RubyCore.Proof.CatchFree [.seqK es] := by
  intro k hk tag
  simp only [List.mem_singleton] at hk
  subst hk
  simp

private theorem seq_escape (es : List RubyCore.Expr) (m : Machine) (j : Jump) :
    Interp.stepFn (deliverA (.esc j) m [.seqK es]) = .next (deliverA (.esc j) m []) := by
  cases j <;> rfl

private theorem seq_bind {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
    {facts mid out : LocalFacts} {current current' : Bool} {e : Ratchet.Expr}
    {es : List RubyCore.Expr} (h : SemFlow κ Γ I facts e σ current κ₁ Γ₁ I₁ mid)
    {m : Machine} (hm : StateOk κ Γ I m) (hf : LocalFactsOk facts m)
    (ht : ∀ n v, StateOk κ₁ Γ₁ I₁ n → denM σ n v → FlowPost mid current v n →
      RunWith n (deliverA (.val v) n [.seqK es]) Γ₂ τ κ₂ I₂ (FlowPost out current')) :
    RunWith m (pushK [.seqK es] (evalFrom m e)) Γ₂ τ κ₂ I₂ (FlowPost out current') := by
  apply (h m hm hf).bind (seq_catchFree es)
  intro a n hr
  cases a with
  | val v => exact (ht n v (hr.1.2.2 v rfl) hr.1.2.1 (hr.2 v rfl)).rebase hr.1.1
  | esc j =>
    apply RunWith.step (by rfl) (seq_escape es n j)
    exact RunWith.answer (fun _ _ c k hp => hp.reCtl c k)
      ⟨⟨hr.1.1, hr.1.2.1, fun _ hv => by cases hv⟩, fun _ hv => by cases hv⟩

private theorem seq_finish {κ : Ctx} {Γ : Env} {I τ : Ty} {m : Machine} {v : Value}
    {out : LocalFacts} {current : Bool} (hm : StateOk κ Γ I m) (hd : denM τ m v)
    (hp : FlowPost out current v m) :
    RunWith m (deliverA (.val v) m [.seqK []]) Γ τ κ I (FlowPost out current) := by
  apply RunWith.step (by rfl) (show Interp.stepFn _ = .next (deliverA (.val v) m []) from rfl)
  exact RunWith.answer (fun _ _ c k hp => hp.reCtl c k)
    ⟨⟨.refl m, hd, fun _ hv => by cases hv; exact hm⟩, fun _ hv => by cases hv; exact hp⟩

theorem SemFlowSeq.runWith {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty}
    {facts out : LocalFacts} {current : Bool} {es : List Ratchet.Expr}
    (h : SemFlowSeq κ Γ I facts es τ current κ' Γ' I' out) :
    ∀ m, StateOk κ Γ I m → LocalFactsOk facts m → ∀ v,
      RunWith m (deliverA (.val v) m [.seqK (toRubyList es)]) Γ' τ κ' I' (FlowPost out current) := by
  induction h with
  | @last κ κ' Γ Γ' I I' τ facts out e current he =>
    intro m hm hf v
    apply RunWith.step (by rfl)
      (show Interp.stepFn _ = .next (pushK [.seqK []] (evalFrom m e)) from rfl)
    exact seq_bind he hm hf (fun _ _ hn hd hp => seq_finish hn hd hp)
  | @cons κ κ₁ κ₂ Γ Γ₁ Γ₂ I I₁ I₂ σ τ f f₁ f₂ e e' es c c' he ht ih =>
    intro m hm hf v
    apply RunWith.step (by rfl)
      (show Interp.stepFn _ = .next (pushK [.seqK (toRubyList (e' :: es))] (evalFrom m e)) from rfl)
    exact seq_bind he hm hf (fun n v hn _ hp => ih n hn hp.1 v)

theorem SemFlow.sequence {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty}
    {facts out : LocalFacts} {current : Bool} {es : List Ratchet.Expr}
    (h : SemFlowSeq κ Γ I facts es τ current κ' Γ' I' out) :
    SemFlow κ Γ I facts (.seq es) τ current κ' Γ' I' out := by
  intro m hm hf
  cases h with
  | @last _ _ _ _ _ _ _ _ _ e _ he =>
    exact RunWith.step (by rfl) (show Interp.stepFn _ = .next (evalFrom m e) from rfl) (he m hm hf)
  | @cons _ _ κ₂ _ _ Γ₂ _ _ I₂ _ τ _ _ f₂ e e' es _ c' he ht =>
    apply RunWith.step (by rfl)
      (show Interp.stepFn _ = .next (pushK [.seqK (toRubyList (e' :: es))] (evalFrom m e)) from rfl)
    exact seq_bind he hm hf (fun n v hn _ hp => ht.runWith n hn hp.1 v)

#print axioms SemFlow.sequence
end Ratchet.Denote.Typed
