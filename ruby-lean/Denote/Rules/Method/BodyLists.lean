import Denote.Rules.Method.BodyContext

/-! Source list companions preserve method-local flow and the callback invariant.
Arguments exclude splat/keyword/forwarding syntax explicitly. Sequence follows the
real flat AST, including the final empty sequence marker. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

inductive SemMethodAll {κ : Ctx} {Γ : Env} {I : Ty}
    (cb : CheckedCallback κ Γ I) (fr : Ratchet.Frame) : Env → List Ratchet.Expr → List Ty → Env → Prop
  | nil {Γm : Env} : SemMethodAll cb fr Γm [] [] Γm
  | cons {Γm Γm' Γm'' : Env} {e : Ratchet.Expr} {es : List Ratchet.Expr} {τ : Ty} {tys : List Ty} :
      SemMethod cb fr Γm e τ Γm' → SemMethodAll cb fr Γm' es tys Γm'' → plainArgB e = true →
      SemMethodAll cb fr Γm (e :: es) (τ :: tys) Γm''

inductive SemMethodSeq {κ : Ctx} {Γ : Env} {I : Ty}
    (cb : CheckedCallback κ Γ I) (fr : Ratchet.Frame) : Env → List Ratchet.Expr → Ty → Env → Prop
  | last {Γm Γm' : Env} {e : Ratchet.Expr} {τ : Ty} :
      SemMethod cb fr Γm e τ Γm' → SemMethodSeq cb fr Γm [e] τ Γm'
  | cons {Γm Γm' Γm'' : Env} {e e' : Ratchet.Expr} {es : List Ratchet.Expr} {σ τ : Ty} :
      SemMethod cb fr Γm e σ Γm' → SemMethodSeq cb fr Γm' (e' :: es) τ Γm'' →
      SemMethodSeq cb fr Γm (e :: e' :: es) τ Γm''

private theorem seq_catchFree (es : List RubyCore.Expr) : RubyCore.Proof.CatchFree [.seqK es] := by
  intro k hk tag
  simp only [List.mem_singleton] at hk
  subst k; simp

private theorem seq_answer {m n : Machine} {Γc Γm : Env} {κc κm : Ctx} {Ic Im τ : Ty} {a : Answer}
    (h : MethodResultOk m Γc Γm τ κc κm Ic Im a n) :
    MethodRunSpec m (deliverA a n [.seqK []]) Γc Γm τ κc κm Ic Im := by
  apply MethodRunSpec.step (next := deliverA a n []) (by cases a <;> rfl) (by
    cases a with
    | val _ => rfl
    | esc j => cases j <;> rfl)
  exact MethodRunSpec.answer h

theorem SemMethodSeq.runSpec {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Ratchet.Frame} {es : List Ratchet.Expr}
    (h : SemMethodSeq cb fr Γm es τ Γm') :
    ∀ origin m, MethodActivation cb fr Γm origin m → ∀ v,
      MethodRunSpec m (deliverA (.val v) m [.seqK (toRubyList es)]) Γ Γm' τ κ
        (callbackMethodCtx κ fr cb.code) I I := by
  induction h with
  | @last Γm Γm' e τ he =>
    intro origin m hm v
    apply MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next
      (pushK [.seqK []] (evalFrom m e)) from rfl)
    exact (he origin m hm).bind (seq_catchFree []) (fun _ _ hr => seq_answer hr)
  | @cons Γm Γm' Γm'' e e' es σ τ he ht ih =>
    intro origin m hm v
    apply MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next
      (pushK [.seqK (toRubyList (e' :: es))] (evalFrom m e)) from rfl)
    apply (he origin m hm).bind (seq_catchFree _)
    intro a n hr
    cases a with
    | val v => exact (ih origin n (hm.after hr) v).rebase hr.1
    | esc j =>
      apply MethodRunSpec.step (next := deliverA (.esc j) n []) (by rfl) (by cases j <;> rfl)
      apply MethodRunSpec.answer (a := .esc j) (n := n)
      exact ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩

theorem SemMethod.sequence {κ : Ctx} {Γ Γm Γm' : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Ratchet.Frame} {es : List Ratchet.Expr}
    (h : SemMethodSeq cb fr Γm es τ Γm') : SemMethod cb fr Γm (.seq es) τ Γm' := by
  intro origin m hm
  cases h with
  | last he =>
    exact MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl) (he origin m hm)
  | cons he ht =>
    apply MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl)
    apply (he origin m hm).bind (seq_catchFree _)
    intro a n hr
    cases a with
    | val v => exact (ht.runSpec origin n (hm.after hr) v).rebase hr.1
    | esc j =>
      apply MethodRunSpec.step (next := deliverA (.esc j) n []) (by rfl) (by cases j <;> rfl)
      apply MethodRunSpec.answer (a := .esc j) (n := n)
      exact ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩

#print axioms SemMethodSeq.runSpec
#print axioms SemMethod.sequence
end Ratchet.Denote.Typed
