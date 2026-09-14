import Denote.Typed.Run

/-! The sequence companion contains semantic premises only. Its interpretation follows
the machine's sequence frames, including the final empty frame. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

inductive SemSeqA : Env → List Ratchet.Expr → Ty → Env → Prop
  | last {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty} :
      SemSafeA Γ e τ Γ' → SemSeqA Γ [e] τ Γ'
  | cons {Γ Γ₁ Γ₂ : Env} {e e' : Ratchet.Expr} {es : List Ratchet.Expr} {σ τ : Ty} :
      SemSafeA Γ e σ Γ₁ → SemSeqA Γ₁ (e' :: es) τ Γ₂ →
      SemSeqA Γ (e :: e' :: es) τ Γ₂

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

private theorem seq_bind {Γ Γ₁ Γ₂ : Env} {e : Ratchet.Expr} {σ τ : Ty}
    {es : List RubyCore.Expr} (h : SemSafeA Γ e σ Γ₁) {m : Machine}
    (hm : StateOk ctx0 Γ .ivar0 m)
    (ht : ∀ n v, StateOk ctx0 Γ₁ .ivar0 n → denM σ n v →
      RunSpec n (deliverA (.val v) n [.seqK es]) Γ₂ τ) :
    RunSpec m (pushK [.seqK es] (evalFrom m e)) Γ₂ τ := by
  apply RunSpec.bind h hm (seq_catchFree es)
  intro a n hr
  cases a with
  | val v => exact (ht n v (hr.2.2 v rfl) hr.2.1).rebase hr.1
  | esc j =>
    apply RunSpec.step (by rfl) (seq_escape es n j)
    exact RunSpec.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩

private theorem seq_finish {Γ : Env} {τ : Ty} {m : Machine} {v : Value}
    (hm : StateOk ctx0 Γ .ivar0 m) (hd : denM τ m v) :
    RunSpec m (deliverA (.val v) m [.seqK []]) Γ τ := by
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next (deliverA (.val v) m []) from rfl)
  exact RunSpec.answer ⟨.refl m, hd, fun _ hv => by cases hv; exact hm⟩

theorem SemSeqA.runSpec {Γ Γ' : Env} {es : List Ratchet.Expr} {τ : Ty}
    (h : SemSeqA Γ es τ Γ') : ∀ m, StateOk ctx0 Γ .ivar0 m → ∀ v,
      RunSpec m (deliverA (.val v) m [.seqK (toRubyList es)]) Γ' τ := by
  induction h with
  | @last Γ Γ' e τ he =>
    intro m hm v
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (pushK [.seqK []] (evalFrom m e)) from rfl)
    exact seq_bind he hm (fun _ _ hn hd => seq_finish hn hd)
  | @cons Γ Γ₁ Γ₂ e e' es σ τ he ht ih =>
    intro m hm v
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ =
        .next (pushK [.seqK (toRubyList (e' :: es))] (evalFrom m e)) from rfl)
    exact seq_bind he hm (fun n v hn _ => ih n hn v)

theorem SemA.seq {Γ Γ' : Env} {es : List Ratchet.Expr} {τ : Ty}
    (h : SemSeqA Γ es τ Γ') : SemSafeA Γ (.seq es) τ Γ' := by
  apply semSafe_of_runSpec
  intro m hm
  cases h with
  | @last _ _ e _ he =>
    exact RunSpec.step (by rfl) (show Interp.stepFn _ = .next (evalFrom m e) from rfl)
      (he.runSpec hm)
  | @cons _ Γ₁ _ e e' es σ _ he ht =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ =
        .next (pushK [.seqK (toRubyList (e' :: es))] (evalFrom m e)) from rfl)
    exact seq_bind he hm (fun n v hn _ => ht.runSpec n hn v)

#print axioms SemA.seq

theorem SemA.DJudgeSeq.last {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : SemSafeA Γ e τ Γ') : SemSeqA Γ [e] τ Γ' := .last h

theorem SemA.DJudgeSeq.cons {Γ Γ₁ Γ₂ : Env} {e e' : Ratchet.Expr}
    {es : List Ratchet.Expr} {σ τ : Ty} (h : SemSafeA Γ e σ Γ₁)
    (ht : SemSeqA Γ₁ (e' :: es) τ Γ₂) : SemSeqA Γ (e :: e' :: es) τ Γ₂ := .cons h ht

end Ratchet.Denote.Typed
