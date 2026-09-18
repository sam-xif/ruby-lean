import Denote.Judgment.Context

/-! Fuel-indexed answer contracts for recursive calls. Both safety and answer typing are
bounded; quantifying over every bound recovers the existing contract exactly. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def RunSpecAt (N : Nat) (origin start : Machine) (Γ : Env) (τ : Ty)
    (κ : Ctx) (I : Ty) : Prop :=
  (∀ fuel, fuel ≤ N → Semantics.typeStuck (Interp.run fuel start) = false) ∧
  ∀ fuel, fuel ≤ N → ∀ a m rest, runA fuel start = .ans a m rest →
    ResultOk origin Γ τ a m κ I

theorem RunSpec.at {origin start : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    (h : RunSpec origin start Γ τ κ I) (N : Nat) : RunSpecAt N origin start Γ τ κ I :=
  ⟨fun fuel _ => h.1 fuel, fun fuel _ => h.2 fuel⟩

theorem runSpec_iff_allAt {origin start : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx} :
    RunSpec origin start Γ τ κ I ↔ ∀ N, RunSpecAt N origin start Γ τ κ I := by
  refine ⟨fun h N => h.at N, fun h => ⟨?_, ?_⟩⟩
  · intro fuel; exact (h fuel).1 fuel (Nat.le_refl _)
  · intro fuel; exact (h fuel).2 fuel (Nat.le_refl _)

theorem RunSpecAt.mono {N M : Nat} {origin start : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    (h : RunSpecAt N origin start Γ τ κ I) (hle : M ≤ N) :
    RunSpecAt M origin start Γ τ κ I :=
  ⟨fun fuel hf => h.1 fuel (Nat.le_trans hf hle), fun fuel hf => h.2 fuel (Nat.le_trans hf hle)⟩

/-- Zero fuel is vacuous only away from an answer point: values already need their type. -/
theorem RunSpecAt.zero {origin start : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    (ha : answerPoint start = none) : RunSpecAt 0 origin start Γ τ κ I := by
  constructor
  · intro fuel hf; have : fuel = 0 := by omega
    subst fuel; rfl
  · intro fuel hf a m rest hr
    have : fuel = 0 := by omega
    subst fuel; rw [runA_zero ha] at hr; cases hr

theorem RunSpecAt.rebase {N : Nat} {origin middle start : Machine} {Γ : Env}
    {τ I : Ty} {κ : Ctx} (h : RunSpecAt N middle start Γ τ κ I)
    (hf : Framed origin middle) : RunSpecAt N origin start Γ τ κ I := by
  refine ⟨h.1, ?_⟩
  intro fuel hn a m rest hr
  obtain ⟨hf', hd, hm⟩ := h.2 fuel hn a m rest hr
  exact ⟨hf.trans hf', hd, hm⟩

theorem RunSpecAt.weaken {N : Nat} {origin start : Machine}
    {κ₁ κ₂ : Ctx} {Γ₁ Γ₂ : Env} {I₁ I₂ σ τ : Ty}
    (h : RunSpecAt N origin start Γ₁ σ κ₁ I₁)
    (hout : ∀ m v, StateOk κ₁ Γ₁ I₁ m → denM σ m v →
      StateOk κ₂ Γ₂ I₂ m ∧ denM τ m v) : RunSpecAt N origin start Γ₂ τ κ₂ I₂ := by
  refine ⟨h.1, ?_⟩
  intro fuel hn a m rest hr
  obtain ⟨hf, hd, hs⟩ := h.2 fuel hn a m rest hr
  cases a with
  | val v =>
    obtain ⟨hm, hv⟩ := hout m v (hs v rfl) hd
    exact ⟨hf, hv, fun _ _ => hm⟩
  | esc j => exact ⟨hf, hd, fun _ hv => by cases hv⟩

/-- The real machine step pays for the strict decrease used at a recursive call. -/
theorem RunSpecAt.step {N : Nat} {origin start next : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    (ha : answerPoint start = none) (hs : Interp.stepFn start = .next next)
    (h : RunSpecAt N origin next Γ τ κ I) : RunSpecAt (N + 1) origin start Γ τ κ I := by
  constructor
  · intro fuel hn
    cases fuel with
    | zero => rfl
    | succ f => rw [run_succ, hs]; exact h.1 f (by omega)
  · intro fuel hn a m rest hr
    cases fuel with
    | zero => rw [runA_zero ha] at hr; cases hr
    | succ f => rw [runA_succ ha, hs] at hr; exact h.2 f (by omega) a m rest hr

theorem RunSpecAt.answer {N : Nat} {origin m : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    {a : Answer} (hr : ResultOk origin Γ τ a m κ I) :
    RunSpecAt N origin (deliverA a m []) Γ τ κ I := (RunSpec.answer hr).at N

theorem RunSpecAt.stepWithin {N : Nat} {origin start next : Machine} {Γ : Env}
    {τ I : Ty} {κ : Ctx} (ha : answerPoint start = none)
    (hs : Interp.stepFn start = .next next) (h : RunSpecAt N origin next Γ τ κ I) :
    RunSpecAt N origin start Γ τ κ I := (RunSpecAt.step ha hs h).mono (Nat.le_succ N)

theorem RunSpecAt.unsupported {N : Nat} {origin start : Machine} {Γ : Env}
    {τ I : Ty} {κ : Ctx} {msg : String}
    (ha : answerPoint start = none) (hs : Interp.stepFn start = .unsupported msg) :
    RunSpecAt N origin start Γ τ κ I := (RunSpec.unsupported ha hs).at N

def StepSpecAt (N : Nat) (origin : Machine) (Γ : Env) (τ : Ty) (step : StepResult)
    (κ : Ctx) (I : Ty) : Prop := match step with
  | .next n => RunSpecAt N origin n Γ τ κ I
  | .unsupported _ => True
  | _ => False

theorem RunSpecAt.of_stepSpec {N : Nat} {origin start : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    (ha : answerPoint start = none) (h : StepSpecAt N origin Γ τ (Interp.stepFn start) κ I) :
    RunSpecAt (N + 1) origin start Γ τ κ I := by
  cases hs : Interp.stepFn start with
  | next n => exact RunSpecAt.step ha hs (by simpa [hs, StepSpecAt] using h)
  | unsupported r => exact RunSpecAt.unsupported ha hs
  | done v n => simp [hs, StepSpecAt] at h
  | uncaught v n => simp [hs, StepSpecAt] at h
  | stuck msg => simp [hs, StepSpecAt] at h

theorem RunSpecAt.of_stepSpecWithin {N : Nat} {origin start : Machine} {Γ : Env}
    {τ I : Ty} {κ : Ctx} (ha : answerPoint start = none)
    (h : StepSpecAt N origin Γ τ (Interp.stepFn start) κ I) :
    RunSpecAt N origin start Γ τ κ I :=
  (RunSpecAt.of_stepSpec ha h).mono (Nat.le_succ N)

/-- Unlike `safe_pushK_le`, neither the inner run nor its answer premise is unbounded.
The continuation gets no more than the original budget, including on escape answers. -/
theorem RunSpecAt.bindSpec {N : Nat} {Γ₁ Γ₂ : Env} {e : Ratchet.Expr} {σ τ : Ty}
    {κ₁ κ₂ : Ctx} {I₁ I₂ : Ty} {m origin : Machine}
    (h : RunSpecAt N m (evalFrom m e) Γ₁ σ κ₁ I₁)
    {K : List Kont} (hK : RubyCore.Proof.CatchFree K)
    (hk : ∀ a n, ResultOk m Γ₁ σ a n κ₁ I₁ →
      RunSpecAt N origin (deliverA a n K) Γ₂ τ κ₂ I₂) :
    RunSpecAt N origin (pushK K (evalFrom m e)) Γ₂ τ κ₂ I₂ := by
  constructor
  · intro fuel hfuel
    rw [run_pushK K hK]
    cases hr : runA fuel (evalFrom m e) with
    | ans a n rest =>
      exact (hk a n (h.2 fuel hfuel a n rest hr)).1 rest
        (Nat.le_trans (runA_rest_le _ _ _ _ _ hr) hfuel)
    | halt hh =>
      have hs := h.1 fuel hfuel
      rw [run_eq_out_nil, hr] at hs
      exact haltBlind_stuck hh [] K hs
    | oof n => rfl
  · intro fuel hfuel a n rest hr
    rw [runA_pushK _ hK] at hr
    cases hs : runA fuel (evalFrom m e) with
    | halt hh => rw [hs] at hr; cases hh <;> cases hr
    | oof n' => rw [hs] at hr; cases hr
    | ans a₁ n₁ r₁ =>
      rw [hs] at hr
      exact (hk a₁ n₁ (h.2 fuel hfuel a₁ n₁ r₁ hs)).2 r₁
        (Nat.le_trans (runA_rest_le _ _ _ _ _ hs) hfuel) a n rest hr

def SemSafeCtxAt (N : Nat) (κ : Ctx) (Γ : Env) (I : Ty) (e : Ratchet.Expr) (τ : Ty)
    (κ' : Ctx) (Γ' : Env) (I' : Ty) : Prop :=
  ∀ m, StateOk κ Γ I m → RunSpecAt N m (evalFrom m e) Γ' τ κ' I'

theorem SemSafeCtxAt.mono {N M : Nat} {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr}
    (h : SemSafeCtxAt N κ Γ I e τ κ' Γ' I') (hle : M ≤ N) :
    SemSafeCtxAt M κ Γ I e τ κ' Γ' I' := fun m hm => (h m hm).mono hle

theorem SemSafeCtxAt.zero {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr} :
    SemSafeCtxAt 0 κ Γ I e τ κ' Γ' I' :=
  fun m _ => RunSpecAt.zero (answerPoint_evalFrom m e)

theorem SemSafeCtxA.at {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr}
    (h : SemSafeCtxA κ Γ I e τ κ' Γ' I') (N : Nat) : SemSafeCtxAt N κ Γ I e τ κ' Γ' I' :=
  fun m hm => (h m hm).at N

theorem semSafeCtxA_iff_allAt {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr} :
    SemSafeCtxA κ Γ I e τ κ' Γ' I' ↔ ∀ N, SemSafeCtxAt N κ Γ I e τ κ' Γ' I' :=
  ⟨fun h N => h.at N, fun h m hm => runSpec_iff_allAt.mpr (fun N => h N m hm)⟩

/-- Recursive-body admission must establish the bounded body from strictly smaller
contracts. An unguarded implication from the body's own full contract is insufficient. -/
theorem semSafeCtxA_of_guarded {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr}
    (step : ∀ N, (∀ n, n < N → SemSafeCtxAt n κ Γ I e τ κ' Γ' I') →
      SemSafeCtxAt N κ Γ I e τ κ' Γ' I') : SemSafeCtxA κ Γ I e τ κ' Γ' I' :=
  semSafeCtxA_iff_allAt.mpr (fun N => Nat.strongRecOn N step)

#print axioms RunSpecAt.bindSpec
#print axioms semSafeCtxA_of_guarded
end Ratchet.Denote.Typed
