import Denote.Judgment.Run

/-! Carry a value postcondition through the real answer/continuation composition.
Safety and framing cover every answer; additional value facts impose nothing on escapes. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def ResultWith (origin : Machine) (Γ : Env) (τ : Ty) (κ : Ctx) (I : Ty)
    (P : Value → Machine → Prop) (a : Answer) (m : Machine) : Prop :=
  ResultOk origin Γ τ a m κ I ∧ ∀ v, a = .val v → P v m

def RunWith (origin start : Machine) (Γ : Env) (τ : Ty) (κ : Ctx) (I : Ty)
    (P : Value → Machine → Prop) : Prop :=
  SafeA start ∧ ∀ fuel a m rest, runA fuel start = .ans a m rest → ResultWith origin Γ τ κ I P a m

theorem RunWith.erase {origin start : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    {P : Value → Machine → Prop} (h : RunWith origin start Γ τ κ I P) :
    RunSpec origin start Γ τ κ I := ⟨h.1, fun f a m r hr => (h.2 f a m r hr).1⟩

theorem RunSpec.withPost {origin start : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    {P : Value → Machine → Prop} (h : RunSpec origin start Γ τ κ I)
    (hp : ∀ v m, ResultOk origin Γ τ (.val v) m κ I → P v m) :
    RunWith origin start Γ τ κ I P := by
  refine ⟨h.1, ?_⟩
  intro fuel a m rest hr
  have ha := h.2 fuel a m rest hr
  exact ⟨ha, fun v hv => hp v m (hv ▸ ha)⟩

theorem RunWith.rebase {origin middle start : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    {P : Value → Machine → Prop} (h : RunWith middle start Γ τ κ I P)
    (hf : Framed origin middle) : RunWith origin start Γ τ κ I P := by
  refine ⟨h.1, ?_⟩
  intro fuel a m rest hr
  obtain ⟨⟨hfr, hd, hs⟩, hp⟩ := h.2 fuel a m rest hr
  exact ⟨⟨hf.trans hfr, hd, hs⟩, hp⟩

theorem RunWith.step {origin start next : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    {P : Value → Machine → Prop} (ha : answerPoint start = none)
    (hs : Interp.stepFn start = .next next) (h : RunWith origin next Γ τ κ I P) :
    RunWith origin start Γ τ κ I P := by
  refine ⟨(h.erase.step ha hs).1, ?_⟩
  intro fuel a m rest hr
  cases fuel with
  | zero => rw [runA_zero ha] at hr; cases hr
  | succ f => rw [runA_succ ha, hs] at hr; exact h.2 f a m rest hr

theorem RunWith.answer {origin m : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    {P : Value → Machine → Prop} {a : Answer}
    (hp : ∀ v n c k, P v n → P v (reCtl n c k))
    (hr : ResultWith origin Γ τ κ I P a m) :
    RunWith origin (deliverA a m []) Γ τ κ I P := by
  refine ⟨(RunSpec.answer hr.1).1, ?_⟩
  intro fuel a' n rest hn
  have hres := (RunSpec.answer hr.1).2 fuel a' n rest hn
  refine ⟨hres, ?_⟩
  rw [runA_ans (a := a) (by cases a <;> rfl)] at hn
  injection hn with h₁ h₂
  cases h₁; cases h₂
  intro v hv
  exact hp v m a.ctl [] (hr.2 v hv)

theorem RunWith.bind {origin m : Machine} {Γ Γ' : Env} {σ τ I I' : Ty} {κ κ' : Ctx}
    {P Q : Value → Machine → Prop} {e : Ratchet.Expr}
    (h : RunWith m (evalFrom m e) Γ σ κ I P)
    {K : List Kont} (hK : RubyCore.Proof.CatchFree K)
    (hk : ∀ a n, ResultWith m Γ σ κ I P a n →
      RunWith origin (deliverA a n K) Γ' τ κ' I' Q) :
    RunWith origin (pushK K (evalFrom m e)) Γ' τ κ' I' Q := by
  constructor
  · exact safe_pushK hK haltBlind_stuck oof_stuck h.1 h.2 (fun a n hn => (hk a n hn).1)
  · intro fuel a n rest hr
    rw [runA_pushK _ hK] at hr
    cases hs : runA fuel (evalFrom m e) with
    | halt hh => rw [hs] at hr; cases hh <;> cases hr
    | oof n' => rw [hs] at hr; cases hr
    | ans a₁ n₁ r₁ =>
      rw [hs] at hr
      exact (hk a₁ n₁ (h.2 fuel a₁ n₁ r₁ hs)).2 r₁ a n rest hr

/-- Consume an intermediate postcondition without imposing it on the final result. -/
theorem RunWith.bindSpec {origin m : Machine} {Γ Γ' : Env} {σ τ I I' : Ty} {κ κ' : Ctx}
    {P : Value → Machine → Prop} {e : Ratchet.Expr}
    (h : RunWith m (evalFrom m e) Γ σ κ I P)
    {K : List Kont} (hK : RubyCore.Proof.CatchFree K)
    (hk : ∀ a n, ResultWith m Γ σ κ I P a n →
      RunSpec origin (deliverA a n K) Γ' τ κ' I') :
    RunSpec origin (pushK K (evalFrom m e)) Γ' τ κ' I' :=
  (h.bind (Q := fun _ _ => True) hK
    (fun a n hn => (hk a n hn).withPost (fun _ _ _ => trivial))).erase

#print axioms RunWith.bind
#print axioms RunWith.bindSpec
end Ratchet.Denote.Typed
