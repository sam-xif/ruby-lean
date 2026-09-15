import Denote.Typed.Context
import Denote.Sem.InitGrow

/-! The initializer's scoped answer contract. Old callers are anchored before allocation;
the running receiver is fresh and writable. Every value answer carries full conformance.
This is not `SemSafeCtxA`: inside initialization the receiver's old field shape may change.
-/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def FreshSelf (anchor : Heap) (m : Machine) : Prop :=
  ∃ o, m.currentFrame.self = .ref o ∧ anchor.objs.size ≤ o ∧
    o < m.heap.objs.size ∧ (m.heap.get o).frozen = false

structure InitState (anchor : Heap) (κ : Ctx) (Γ : Env) (I : Ty) (m : Machine) : Prop where
  typed : StateOk κ Γ I m
  growth : InitGrow anchor m.heap
  fresh : FreshSelf anchor m

structure InitFrame (anchor : Heap) (m n : Machine) : Prop where
  growth : InitGrow anchor n.heap
  stack : n.stack = m.stack
  frames : FramePres m n

def InitResultOk (anchor : Heap) (origin : Machine) (Γ : Env) (τ : Ty)
    (a : Answer) (n : Machine) (κ : Ctx) (I : Ty) : Prop :=
  InitFrame anchor origin n ∧ AnsOk τ n a ∧ (∀ v, a = .val v → InitState anchor κ Γ I n)

def InitRunSpec (anchor : Heap) (origin start : Machine) (Γ : Env) (τ : Ty)
    (κ : Ctx) (I : Ty) : Prop :=
  SafeA start ∧ ∀ fuel a n rest, runA fuel start = .ans a n rest →
    InitResultOk anchor origin Γ τ a n κ I

def SemInitA (κ : Ctx) (Γ : Env) (I : Ty) (e : Ratchet.Expr) (τ : Ty)
    (κ' : Ctx) (Γ' : Env) (I' : Ty) : Prop :=
  ∀ anchor m, InitState anchor κ Γ I m → InitRunSpec anchor m (evalFrom m e) Γ' τ κ' I'

theorem InitState.reCtl {anchor : Heap} {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (h : InitState anchor κ Γ I m) (c : Ctl) (ks : List Kont) :
    InitState anchor κ Γ I (reCtl m c ks) :=
  ⟨StateOk_reCtl h.typed c ks, h.growth, h.fresh⟩

theorem InitFrame.refl {anchor : Heap} {m : Machine} (hg : InitGrow anchor m.heap) :
    InitFrame anchor m m := ⟨hg, rfl, .refl m⟩

theorem InitFrame.reCtl {anchor : Heap} {m n : Machine} (h : InitFrame anchor m n)
    (c : Ctl) (ks : List Kont) : InitFrame anchor m (reCtl n c ks) :=
  ⟨h.growth, h.stack, h.frames.trans (.of_eq rfl rfl) h.stack⟩

theorem InitFrame.trans {anchor : Heap} {m n p : Machine}
    (h : InitFrame anchor m n) (h' : InitFrame anchor n p) : InitFrame anchor m p :=
  ⟨h'.growth, h'.stack.trans h.stack, h.frames.trans h'.frames h.stack⟩

theorem InitRunSpec.rebase {anchor : Heap} {origin middle start : Machine}
    {κ : Ctx} {Γ : Env} {τ I : Ty} (h : InitRunSpec anchor middle start Γ τ κ I)
    (hf : InitFrame anchor origin middle) : InitRunSpec anchor origin start Γ τ κ I := by
  refine ⟨h.1, ?_⟩
  intro fuel a n rest hr
  obtain ⟨hf', ha, hn⟩ := h.2 fuel a n rest hr
  exact ⟨hf.trans hf', ha, hn⟩

theorem InitRunSpec.step {anchor : Heap} {origin start next : Machine} {κ : Ctx}
    {Γ : Env} {τ I : Ty} (ha : answerPoint start = none)
    (hs : Interp.stepFn start = .next next) (h : InitRunSpec anchor origin next Γ τ κ I) :
    InitRunSpec anchor origin start Γ τ κ I := by
  constructor
  · intro fuel
    cases fuel with
    | zero => rfl
    | succ f => rw [run_succ, hs]; exact h.1 f
  · intro fuel a n rest hr
    cases fuel with
    | zero => rw [runA_zero ha] at hr; cases hr
    | succ f => rw [runA_succ ha, hs] at hr; exact h.2 f a n rest hr

theorem InitRunSpec.answer {anchor : Heap} {origin m : Machine} {κ : Ctx}
    {Γ : Env} {τ I : Ty} {a : Answer} (h : InitResultOk anchor origin Γ τ a m κ I) :
    InitRunSpec anchor origin (deliverA a m []) Γ τ κ I := by
  constructor
  · cases a with
    | val v => exact safeA_value_nil m v
    | esc j => exact safeA_escape_kontOk (DKontOk.nil (τa := τ) (Γ := Γ)) m j h.2.1
  · intro fuel a' n rest hr
    rw [runA_ans (a := a) (by cases a <;> rfl)] at hr
    injection hr with h₁ h₂
    cases h₁; cases h₂
    refine ⟨h.1.reCtl _ _, ?_, ?_⟩
    · cases a with
      | val v => exact denM_deliverA.mpr h.2.1
      | esc j => exact h.2.1
    · intro v hv; exact (h.2.2 v hv).reCtl _ _

theorem InitRunSpec.bindSpec {anchor : Heap} {m origin : Machine} {e : Ratchet.Expr}
    {κ₁ κ₂ : Ctx} {Γ₁ Γ₂ : Env} {I₁ I₂ σ τ : Ty}
    (h : InitRunSpec anchor m (evalFrom m e) Γ₁ σ κ₁ I₁)
    {K : List Kont} (hK : RubyCore.Proof.CatchFree K)
    (hk : ∀ a n, InitResultOk anchor m Γ₁ σ a n κ₁ I₁ →
      InitRunSpec anchor origin (deliverA a n K) Γ₂ τ κ₂ I₂) :
    InitRunSpec anchor origin (pushK K (evalFrom m e)) Γ₂ τ κ₂ I₂ := by
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

/-- Exit initialization by composing its scoped result contract with an ordinary caller
continuation. The continuation must publish the preallocation frame and typed result. -/
theorem InitRunSpec.bindRunSpec {anchor : Heap} {m origin : Machine} {e : Ratchet.Expr}
    {κ₁ κ₂ : Ctx} {Γ₁ Γ₂ : Env} {I₁ I₂ σ τ : Ty}
    (h : InitRunSpec anchor m (evalFrom m e) Γ₁ σ κ₁ I₁)
    {K : List Kont} (hK : RubyCore.Proof.CatchFree K)
    (hk : ∀ a n, InitResultOk anchor m Γ₁ σ a n κ₁ I₁ →
      RunSpec origin (deliverA a n K) Γ₂ τ κ₂ I₂) :
    RunSpec origin (pushK K (evalFrom m e)) Γ₂ τ κ₂ I₂ := by
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

theorem InitRunSpec.weaken {anchor : Heap} {origin start : Machine} {κ₁ κ₂ : Ctx}
    {Γ₁ Γ₂ : Env} {I₁ I₂ σ τ : Ty} (h : InitRunSpec anchor origin start Γ₁ σ κ₁ I₁)
    (hout : ∀ m v, InitState anchor κ₁ Γ₁ I₁ m → denM σ m v →
      InitState anchor κ₂ Γ₂ I₂ m ∧ denM τ m v) :
    InitRunSpec anchor origin start Γ₂ τ κ₂ I₂ := by
  refine ⟨h.1, ?_⟩
  intro fuel a n rest hr
  obtain ⟨hf, ha, hn⟩ := h.2 fuel a n rest hr
  cases a with
  | val v =>
    obtain ⟨hs, hv⟩ := hout n v (hn v rfl) ha
    exact ⟨hf, hv, fun _ _ => hs⟩
  | esc j => exact ⟨hf, ha, fun _ hv => by cases hv⟩

#print axioms InitRunSpec.bindSpec
#print axioms InitRunSpec.bindRunSpec
#print axioms InitRunSpec.weaken
end Ratchet.Denote.Typed
