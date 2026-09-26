import Denote.Rules.Method.Flow

/-! Flat source sequences thread callback aliases and full method environments.
The next expression consumes facts proved at the preceding expression's actual answer. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

inductive SemMethodFlowSeq {κ : Ctx} {Γ : Env} {I : Ty}
    (cb : CheckedCallback κ Γ I) (fr : Ratchet.Frame) : Env → CallbackFacts →
      List Ratchet.Expr → Ty → Bool → Env → CallbackFacts → Prop
  | last {Γm Γm' : Env} {facts out : CallbackFacts} {e : Ratchet.Expr} {τ : Ty} {callback : Bool} :
      SemMethodFlow cb fr Γm facts e τ callback Γm' out →
      SemMethodFlowSeq cb fr Γm facts [e] τ callback Γm' out
  | cons {Γm Γm' Γm'' : Env} {facts mid out : CallbackFacts}
      {e e' : Ratchet.Expr} {es : List Ratchet.Expr} {σ τ : Ty} {c c' : Bool} :
      SemMethodFlow cb fr Γm facts e σ c Γm' mid →
      SemMethodFlowSeq cb fr Γm' mid (e' :: es) τ c' Γm'' out →
      SemMethodFlowSeq cb fr Γm facts (e :: e' :: es) τ c' Γm'' out

private theorem seq_catchFree (es : List RubyCore.Expr) : RubyCore.Proof.CatchFree [.seqK es] := by
  intro k hk tag
  simp only [List.mem_singleton] at hk
  subst k; simp

private theorem seq_answer {m n : Machine} {Γc Γm : Env} {κc κm : Ctx} {Ic Im τ : Ty} {a : Answer}
    {facts : CallbackFacts} {callback : Bool}
    (h : MethodResultWith m Γc Γm τ κc κm Ic Im (CallbackPost facts callback) a n) :
    MethodRunWith m (deliverA a n [.seqK []]) Γc Γm τ κc κm Ic Im
      (CallbackPost facts callback) := by
  apply MethodRunWith.step (next := deliverA a n []) (by cases a <;> rfl) (by
    cases a with
    | val _ => rfl
    | esc j => cases j <;> rfl)
  exact MethodRunWith.answer (fun _ _ c k h => h.reCtl c k) h

theorem SemMethodFlowSeq.runWith {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Ratchet.Frame} {es : List Ratchet.Expr}
    {facts out : CallbackFacts} {callback : Bool}
    (h : SemMethodFlowSeq cb fr Γm facts es τ callback Γm' out) :
    ∀ origin m, MethodActivation cb fr Γm origin m → CallbackFactsOk facts m → ∀ v,
      MethodRunWith m (deliverA (.val v) m [.seqK (toRubyList es)]) Γ Γm' τ κ
        (callbackMethodCtx κ fr cb.code) I I (CallbackPost out callback) := by
  induction h with
  | @last Γm Γm' facts out e τ callback he =>
    intro origin m hm hf v
    apply MethodRunWith.step (by rfl) (show Interp.stepFn _ = .next
      (pushK [.seqK []] (evalFrom m e)) from rfl)
    exact (he origin m hm hf).bind (seq_catchFree []) (fun _ _ hr => seq_answer hr)
  | @cons Γm Γm' Γm'' facts mid out e e' es σ τ c c' he ht ih =>
    intro origin m hm hf v
    apply MethodRunWith.step (by rfl) (show Interp.stepFn _ = .next
      (pushK [.seqK (toRubyList (e' :: es))] (evalFrom m e)) from rfl)
    apply (he origin m hm hf).bind (seq_catchFree _)
    intro a n hr
    cases a with
    | val v => exact (ih origin n (hm.after hr.1) (hr.2 v rfl).1 v).rebase hr.1.1
    | esc j =>
      apply MethodRunWith.step (next := deliverA (.esc j) n []) (by rfl) (by cases j <;> rfl)
      exact MethodRunWith.answer (fun _ _ c k h => h.reCtl c k)
        ⟨⟨hr.1.1, hr.1.2.1, fun _ hv => by cases hv⟩, fun _ hv => by cases hv⟩

theorem SemMethodFlow.sequence {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Ratchet.Frame} {es : List Ratchet.Expr}
    {facts out : CallbackFacts} {callback : Bool}
    (h : SemMethodFlowSeq cb fr Γm facts es τ callback Γm' out) :
    SemMethodFlow cb fr Γm facts (.seq es) τ callback Γm' out := by
  intro origin m hm hf
  cases h with
  | last he =>
    exact MethodRunWith.step (by rfl) (show Interp.stepFn _ = .next _ from rfl) (he origin m hm hf)
  | cons he ht =>
    apply MethodRunWith.step (by rfl) (show Interp.stepFn _ = .next _ from rfl)
    apply (he origin m hm hf).bind (seq_catchFree _)
    intro a n hr
    cases a with
    | val v => exact (ht.runWith origin n (hm.after hr.1) (hr.2 v rfl).1 v).rebase hr.1.1
    | esc j =>
      apply MethodRunWith.step (next := deliverA (.esc j) n []) (by rfl) (by cases j <;> rfl)
      exact MethodRunWith.answer (fun _ _ c k h => h.reCtl c k)
        ⟨⟨hr.1.1, hr.1.2.1, fun _ hv => by cases hv⟩, fun _ hv => by cases hv⟩

#print axioms SemMethodFlow.sequence
end Ratchet.Denote.Typed
