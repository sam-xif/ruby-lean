import Denote.Typed.Compose

/-! The existing answer contract at an explicit machine entry. List evaluation starts under
an argument or sequence frame, so its entry is not always `evalFrom`. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def ResultOk (origin : Machine) (Γ : Env) (τ : Ty) (a : Answer) (m : Machine) : Prop :=
  Framed origin m ∧ AnsOk τ m a ∧ (∀ v, a = .val v → StateOk ctx0 Γ .ivar0 m)

def RunSpec (origin start : Machine) (Γ : Env) (τ : Ty) : Prop :=
  SafeA start ∧ ∀ fuel a m rest, runA fuel start = .ans a m rest → ResultOk origin Γ τ a m

theorem RunSpec.rebase {origin middle start : Machine} {Γ : Env} {τ : Ty}
    (h : RunSpec middle start Γ τ) (hf : Framed origin middle) :
    RunSpec origin start Γ τ := by
  refine ⟨h.1, ?_⟩
  intro fuel a m rest hr
  obtain ⟨hf', hd, hm⟩ := h.2 fuel a m rest hr
  exact ⟨hf.trans hf', hd, hm⟩

theorem RunSpec.step {origin start next : Machine} {Γ : Env} {τ : Ty}
    (ha : answerPoint start = none) (hs : Interp.stepFn start = .next next)
    (h : RunSpec origin next Γ τ) : RunSpec origin start Γ τ := by
  constructor
  · intro fuel
    cases fuel with
    | zero => rfl
    | succ f => rw [run_succ, hs]; exact h.1 f
  · intro fuel a m rest hr
    cases fuel with
    | zero => rw [runA_zero ha] at hr; cases hr
    | succ f => rw [runA_succ ha, hs] at hr; exact h.2 f a m rest hr

theorem RunSpec.unsupported {origin start : Machine} {Γ : Env} {τ : Ty} {msg : String}
    (ha : answerPoint start = none) (hs : Interp.stepFn start = .unsupported msg) :
    RunSpec origin start Γ τ := by
  constructor
  · intro fuel
    cases fuel with
    | zero => rfl
    | succ f => rw [run_succ, hs]; rfl
  · intro fuel a m rest hr
    cases fuel with
    | zero => rw [runA_zero ha] at hr; cases hr
    | succ f => rw [runA_succ ha, hs] at hr; cases hr

theorem SemSafeA.runSpec {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : SemSafeA Γ e τ Γ') {m : Machine} (hm : StateOk ctx0 Γ .ivar0 m) :
    RunSpec m (evalFrom m e) Γ' τ := ⟨h.closed hm, h.1 m hm⟩

theorem semSafe_of_runSpec {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : ∀ m, StateOk ctx0 Γ .ivar0 m → RunSpec m (evalFrom m e) Γ' τ) :
    SemSafeA Γ e τ Γ' :=
  ⟨fun m hm => (h m hm).2,
    safeUnder_of_closed (fun m hm => (h m hm).2) (fun m hm => (h m hm).1)⟩

theorem RunSpec.answer {origin m : Machine} {Γ : Env} {τ : Ty} {a : Answer}
    (hr : ResultOk origin Γ τ a m) : RunSpec origin (deliverA a m []) Γ τ := by
  constructor
  · cases a with
    | val v => exact safeA_value_nil m v
    | esc j => exact safeA_escape_kontOk (DKontOk.nil (τa := τ) (Γ := Γ)) m j hr.2.1
  · intro fuel a' n rest hn
    rw [runA_ans (a := a) (by cases a <;> rfl)] at hn
    injection hn with h₁ h₂
    cases h₁; cases h₂
    refine ⟨hr.1.trans (Framed_reCtl _ _ _), ?_, ?_⟩
    · cases a with
      | val v => exact denM_deliverA.mpr hr.2.1
      | esc j => cases j <;> simpa [AnsOk, EscOk, deliverA] using hr.2.1
    · intro v hv; exact StateOk_deliverA (hr.2.2 v hv)

/-- Compose one expression with a continuation contract. Halts remain covered by the
safety premise, and the continuation receives the complete answer contract. -/
theorem RunSpec.bind {Γ Γ₁ Γ₂ : Env} {e : Ratchet.Expr} {σ τ : Ty}
    (h : SemSafeA Γ e σ Γ₁) {m : Machine} (hm : StateOk ctx0 Γ .ivar0 m)
    {K : List Kont} (hK : RubyCore.Proof.CatchFree K)
    (hk : ∀ a n, ResultOk m Γ₁ σ a n → RunSpec m (deliverA a n K) Γ₂ τ) :
    RunSpec m (pushK K (evalFrom m e)) Γ₂ τ := by
  constructor
  · exact safe_pushK hK haltBlind_stuck oof_stuck (h.closed hm)
      (h.1 m hm) (fun a n hn => (hk a n hn).1)
  · intro fuel a n rest hr
    rw [runA_pushK _ hK] at hr
    cases hs : runA fuel (evalFrom m e) with
    | halt hh => rw [hs] at hr; cases hh <;> cases hr
    | oof n' => rw [hs] at hr; cases hr
    | ans a₁ n₁ r₁ =>
      rw [hs] at hr
      exact (hk a₁ n₁ (h.1 m hm fuel a₁ n₁ r₁ hs)).2 r₁ a n rest hr

#print axioms RunSpec.bind
end Ratchet.Denote.Typed
