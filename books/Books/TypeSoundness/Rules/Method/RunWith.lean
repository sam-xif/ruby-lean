import Books.TypeSoundness.Rules.Method.BodyRun

/-! Value postconditions at the mixed method/callback boundary. Both complete
environments and the existing MethodEffects contract remain mandatory. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def MethodResultWith (origin : Machine) (Γc Γm : Env) (τ : Ty) (κc κm : Ctx) (Ic Im : Ty)
    (P : Value → Machine → Prop) (a : Answer) (m : Machine) : Prop :=
  MethodResultOk origin Γc Γm τ κc κm Ic Im a m ∧ ∀ v, a = .val v → P v m

def MethodRunWith (origin start : Machine) (Γc Γm : Env) (τ : Ty) (κc κm : Ctx) (Ic Im : Ty)
    (P : Value → Machine → Prop) : Prop :=
  SafeA start ∧ ∀ fuel a m rest, runA fuel start = .ans a m rest →
    MethodResultWith origin Γc Γm τ κc κm Ic Im P a m

theorem MethodRunWith.erase {origin start : Machine} {Γc Γm : Env} {τ Ic Im : Ty} {κc κm : Ctx}
    {P : Value → Machine → Prop} (h : MethodRunWith origin start Γc Γm τ κc κm Ic Im P) :
    MethodRunSpec origin start Γc Γm τ κc κm Ic Im :=
  ⟨h.1, fun f a m r hr => (h.2 f a m r hr).1⟩

theorem MethodRunSpec.withPost {origin start : Machine} {Γc Γm : Env} {τ Ic Im : Ty} {κc κm : Ctx}
    {P : Value → Machine → Prop} (h : MethodRunSpec origin start Γc Γm τ κc κm Ic Im)
    (hp : ∀ v m, MethodResultOk origin Γc Γm τ κc κm Ic Im (.val v) m → P v m) :
    MethodRunWith origin start Γc Γm τ κc κm Ic Im P := by
  refine ⟨h.1, ?_⟩
  intro f a m r hr
  have ha := h.2 f a m r hr
  exact ⟨ha, fun v hv => hp v m (hv ▸ ha)⟩

theorem MethodRunWith.mapPost {origin start : Machine} {Γc Γm : Env} {τ Ic Im : Ty} {κc κm : Ctx}
    {P Q : Value → Machine → Prop} (h : MethodRunWith origin start Γc Γm τ κc κm Ic Im P)
    (hp : ∀ v m, MethodResultOk origin Γc Γm τ κc κm Ic Im (.val v) m → P v m → Q v m) :
    MethodRunWith origin start Γc Γm τ κc κm Ic Im Q := by
  refine ⟨h.1, ?_⟩
  intro f a m r hr
  have ha := h.2 f a m r hr
  exact ⟨ha.1, fun v hv => hp v m (hv ▸ ha.1) (ha.2 v hv)⟩

theorem MethodRunWith.rebase {origin middle start : Machine} {Γc Γm : Env} {τ Ic Im : Ty}
    {κc κm : Ctx} {P : Value → Machine → Prop}
    (h : MethodRunWith middle start Γc Γm τ κc κm Ic Im P) (hf : MethodEffects origin middle) :
    MethodRunWith origin start Γc Γm τ κc κm Ic Im P := by
  refine ⟨h.1, ?_⟩
  intro f a m r hr
  obtain ⟨⟨hfr, hd, hs⟩, hp⟩ := h.2 f a m r hr
  exact ⟨⟨hf.trans hfr, hd, hs⟩, hp⟩

theorem MethodRunWith.step {origin start next : Machine} {Γc Γm : Env} {τ Ic Im : Ty} {κc κm : Ctx}
    {P : Value → Machine → Prop} (ha : answerPoint start = none)
    (hs : Interp.stepFn start = .next next) (h : MethodRunWith origin next Γc Γm τ κc κm Ic Im P) :
    MethodRunWith origin start Γc Γm τ κc κm Ic Im P := by
  refine ⟨(h.erase.step ha hs).1, ?_⟩
  intro fuel a m rest hr
  cases fuel with
  | zero => rw [runA_zero ha] at hr; cases hr
  | succ f => rw [runA_succ ha, hs] at hr; exact h.2 f a m rest hr

theorem MethodRunWith.answer {origin m : Machine} {Γc Γm : Env} {τ Ic Im : Ty} {κc κm : Ctx}
    {P : Value → Machine → Prop} {a : Answer}
    (hp : ∀ v n c k, P v n → P v (reCtl n c k))
    (hr : MethodResultWith origin Γc Γm τ κc κm Ic Im P a m) :
    MethodRunWith origin (deliverA a m []) Γc Γm τ κc κm Ic Im P := by
  refine ⟨(MethodRunSpec.answer hr.1).1, ?_⟩
  intro fuel a' n rest hn
  have hres := (MethodRunSpec.answer hr.1).2 fuel a' n rest hn
  refine ⟨hres, ?_⟩
  rw [runA_ans (a := a) (by cases a <;> rfl)] at hn
  injection hn with h₁ h₂
  cases h₁; cases h₂
  intro v hv
  exact hp v m a.ctl [] (hr.2 v hv)

theorem MethodRunWith.bind {origin m : Machine} {Γc Γm Γc' Γm' : Env}
    {σ τ Ic Im Ic' Im' : Ty} {κc κm κc' κm' : Ctx}
    {P Q : Value → Machine → Prop} {e : Checker.Expr}
    (h : MethodRunWith m (evalFrom m e) Γc Γm σ κc κm Ic Im P)
    (hroot : RootClean m)
    {K : List Kont} (hK : RubyCore.Proof.CatchFree K)
    (hk : ∀ a n, MethodResultWith m Γc Γm σ κc κm Ic Im P a n →
      MethodRunWith origin (deliverA a n K) Γc' Γm' τ κc' κm' Ic' Im' Q) :
    MethodRunWith origin (pushK K (evalFrom m e)) Γc' Γm' τ κc' κm' Ic' Im' Q := by
  constructor
  · exact safe_pushK hK haltBlind_stuck oof_stuck h.1 h.2 (fun a n hn => (hk a n hn).1) hroot
      (fun _ _ hn => hn.1.1.rootClean hroot)
  · intro fuel a n rest hr
    rw [runA_pushK _ hK fuel (evalFrom m e) hroot
      (fun a n r hr => (h.2 fuel a n r hr).1.1.rootClean hroot)] at hr
    cases hs : runA fuel (evalFrom m e) with
    | halt hh => rw [hs] at hr; cases hh <;> cases hr
    | oof _ => rw [hs] at hr; cases hr
    | ans a₁ n₁ r₁ =>
      rw [hs] at hr
      exact (hk a₁ n₁ (h.2 fuel a₁ n₁ r₁ hs)).2 r₁ a n rest hr

theorem RunSpec.bindMethodWith {origin m : Machine} {Γ Γc Γm : Env} {σ τ I Ic Im : Ty}
    {κ κc κm : Ctx} {e : Checker.Expr} {P : Value → Machine → Prop}
    (h : RunSpec m (evalFrom m e) Γ σ κ I)
    (hroot : RootClean m)
    {K : List Kont} (hK : RubyCore.Proof.CatchFree K)
    (hk : ∀ a n, ResultOk m Γ σ a n κ I →
      MethodRunWith origin (deliverA a n K) Γc Γm τ κc κm Ic Im P) :
    MethodRunWith origin (pushK K (evalFrom m e)) Γc Γm τ κc κm Ic Im P := by
  constructor
  · exact safe_pushK hK haltBlind_stuck oof_stuck h.1 h.2 (fun a n hn => (hk a n hn).1) hroot
      (fun _ _ hn => hn.1.rootClean hroot)
  · intro fuel a n rest hr
    rw [runA_pushK _ hK fuel (evalFrom m e) hroot
      (fun a n r hr => (h.2 fuel a n r hr).1.rootClean hroot)] at hr
    cases hs : runA fuel (evalFrom m e) with
    | halt hh => rw [hs] at hr; cases hh <;> cases hr
    | oof _ => rw [hs] at hr; cases hr
    | ans a₁ n₁ r₁ =>
      rw [hs] at hr
      exact (hk a₁ n₁ (h.2 fuel a₁ n₁ r₁ hs)).2 r₁ a n rest hr

#print axioms MethodRunWith.bind
#print axioms RunSpec.bindMethodWith
end Checker.Soundness.Typed
