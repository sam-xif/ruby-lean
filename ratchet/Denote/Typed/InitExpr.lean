import Denote.Typed.InitRun
import Denote.Typed.InstanceWrite

/-! Compositional initializer semantics. Write conformance is a premise to discharge,
not an unchecked assumption supplied by a method signature. No checker rules are added here.
-/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemInitA.var {κ : Ctx} {Γ : Env} {I τ : Ty} {x : String}
    (hx : envGet? Γ x = some τ) (ha : isAliasTy τ = false) :
    SemInitA κ Γ I (.var .lvar x) τ κ Γ I := by
  intro anchor m hm
  apply InitRunSpec.step (answerPoint_evalFrom _ _) (stepFn_var m x)
  exact InitRunSpec.answer (a := .val (m.getLocal x))
    ⟨.refl hm.growth, denM_getLocal hm.typed hx ha, fun _ _ => hm⟩

theorem SemInitA.ignoreResult {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr}
    (h : SemInitA κ Γ I e τ κ' Γ' I') : SemInitA κ Γ I e .any κ' Γ' I' :=
  fun anchor m hm => (h anchor m hm).weaken (fun _ _ hn _ => ⟨hn, by simp [denM]⟩)

theorem SemInitA.ivarAsgn {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ ρ : Ty}
    {x : String} {e : Ratchet.Expr} (he : SemInitA κ Γ I e ρ κ₁ Γ₁ I₁)
    (hw : ∀ anchor m v, InitState anchor κ₁ Γ₁ I₁ m → denM ρ m v →
      InitState anchor κ₂ Γ₂ I₂ (Interp.bindIvar m x v) ∧
        denM ρ (Interp.bindIvar m x v) v) :
    SemInitA κ Γ I (.vasgn .ivar x e) ρ κ₂ Γ₂ I₂ := by
  intro anchor m hm
  apply InitRunSpec.step (answerPoint_evalFrom _ _) (show Interp.stepFn _ =
    .next (pushK [.asgnK .ivar x] (evalFrom m e)) from rfl)
  apply (he anchor m hm).bindSpec (by intro k hk tag; simp only [List.mem_singleton] at hk; subst k; simp)
  intro a n hr
  cases a with
  | val v =>
    have hn := hr.2.2 v rfl
    obtain ⟨o, hs, _, _, hf⟩ := hn.fresh
    obtain ⟨hn', hv⟩ := hw anchor n v hn hr.2.1
    apply InitRunSpec.step (by rfl) (stepFn_ivarWrite hs hf)
    exact InitRunSpec.answer (a := .val v) ⟨hr.1.trans ⟨hn'.growth, by simp, .bindIvar n x v⟩,
      hv, fun _ _ => hn'⟩
  | esc j =>
    apply InitRunSpec.step (by rfl) (show Interp.stepFn _ =
      .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact InitRunSpec.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩

inductive SemInitSeqA : Ctx → Env → Ty → List Ratchet.Expr → Ty → Ctx → Env → Ty → Prop
  | last {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr} :
      SemInitA κ Γ I e τ κ' Γ' I' → SemInitSeqA κ Γ I [e] τ κ' Γ' I'
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
      {e e' : Ratchet.Expr} {es : List Ratchet.Expr} :
      SemInitA κ Γ I e σ κ₁ Γ₁ I₁ → SemInitSeqA κ₁ Γ₁ I₁ (e' :: es) τ κ₂ Γ₂ I₂ →
      SemInitSeqA κ Γ I (e :: e' :: es) τ κ₂ Γ₂ I₂

private theorem init_seq_bind {anchor : Heap} {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env}
    {I I₁ I₂ σ τ : Ty} {e : Ratchet.Expr} {es : List RubyCore.Expr}
    (h : SemInitA κ Γ I e σ κ₁ Γ₁ I₁) {m : Machine} (hm : InitState anchor κ Γ I m)
    (ht : ∀ n v, InitState anchor κ₁ Γ₁ I₁ n → denM σ n v →
      InitRunSpec anchor n (deliverA (.val v) n [.seqK es]) Γ₂ τ κ₂ I₂) :
    InitRunSpec anchor m (pushK [.seqK es] (evalFrom m e)) Γ₂ τ κ₂ I₂ := by
  apply (h anchor m hm).bindSpec (by intro k hk tag; simp only [List.mem_singleton] at hk; subst k; simp)
  intro a n hr
  cases a with
  | val v => exact (ht n v (hr.2.2 v rfl) hr.2.1).rebase hr.1
  | esc j =>
    apply InitRunSpec.step (by rfl) (show Interp.stepFn _ =
      .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact InitRunSpec.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩

private theorem init_seq_finish {anchor : Heap} {κ : Ctx} {Γ : Env} {I τ : Ty}
    {m : Machine} {v : Value} (hm : InitState anchor κ Γ I m) (hd : denM τ m v) :
    InitRunSpec anchor m (deliverA (.val v) m [.seqK []]) Γ τ κ I := by
  apply InitRunSpec.step (by rfl) (show Interp.stepFn _ = .next (deliverA (.val v) m []) from rfl)
  exact InitRunSpec.answer ⟨.refl hm.growth, hd, fun _ _ => hm⟩

theorem SemInitSeqA.runSpec {anchor : Heap} {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty}
    {es : List Ratchet.Expr} (h : SemInitSeqA κ Γ I es τ κ' Γ' I') :
    ∀ m, InitState anchor κ Γ I m → ∀ v,
      InitRunSpec anchor m (deliverA (.val v) m [.seqK (toRubyList es)]) Γ' τ κ' I' := by
  induction h with
  | @last κ κ' Γ Γ' I I' τ e he =>
    intro m hm v
    apply InitRunSpec.step (by rfl) (show Interp.stepFn _ =
      .next (pushK [.seqK []] (evalFrom m e)) from rfl)
    exact init_seq_bind he hm (fun _ _ hn hd => init_seq_finish hn hd)
  | @cons κ κ₁ κ₂ Γ Γ₁ Γ₂ I I₁ I₂ σ τ e e' es he ht ih =>
    intro m hm v
    apply InitRunSpec.step (by rfl) (show Interp.stepFn _ =
      .next (pushK [.seqK (toRubyList (e' :: es))] (evalFrom m e)) from rfl)
    exact init_seq_bind he hm (fun n v hn _ => ih n hn v)

theorem SemInitA.sequence {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {es : List Ratchet.Expr}
    (h : SemInitSeqA κ Γ I es τ κ' Γ' I') : SemInitA κ Γ I (.seq es) τ κ' Γ' I' := by
  intro anchor m hm
  cases h with
  | @last _ _ _ _ _ _ _ e he =>
    exact InitRunSpec.step (by rfl) (show Interp.stepFn _ = .next (evalFrom m e) from rfl)
      (he anchor m hm)
  | @cons _ _ _ _ Γ₁ _ _ _ _ σ _ e e' es he ht =>
    apply InitRunSpec.step (by rfl) (show Interp.stepFn _ =
      .next (pushK [.seqK (toRubyList (e' :: es))] (evalFrom m e)) from rfl)
    exact init_seq_bind he hm (fun n v hn _ => ht.runSpec n hn v)

#print axioms SemInitA.ivarAsgn
#print axioms SemInitA.sequence
end Ratchet.Denote.Typed
