import Denote.Rules.Closure.Entry
import Denote.Rules.Method.MethodReturn

/-! The real block continuation consumes the strengthened answer contract. Captured
writes still require caller restoration; this file does not assume method-frame isolation. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem step_blkFrameK_value (n : Machine) (fid : FrameId) (lam : Bool)
    (brk : Option FrameId) (cl : Closure) (args : List Value) (v : Value) {K : List Kont} :
    Interp.stepFn (deliverA (.val v) n (.blkFrameK fid lam brk cl args :: K)) =
      .next (deliverA (.val v) (popMethodFrame n) K) := rfl

/-- Only an exception can escape a currently certified body. It crosses the block
continuation unchanged, with the block activation popped. -/
theorem blkFrameK_escape {origin n : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    {K : List Kont} (fid : FrameId) (lam : Bool) (brk : Option FrameId)
    (cl : Closure) (args : List Value) (j : Jump) (he : EscOk n j)
    (hr : RunSpec origin (deliverA (.esc j) (popMethodFrame n) K) Γ τ κ I) :
    RunSpec origin (deliverA (.esc j) n (.blkFrameK fid lam brk cl args :: K)) Γ τ κ I := by
  obtain ⟨exc, rfl, _⟩ := he.only_raise
  exact RunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl) hr

/-- The block marker handles the complete answer. Caller framing is needed on every
answer, and full caller conformance on values; neither follows from a captured body's
FramePres.isolated clause. First-order results survive the stack pop at an unchanged heap. -/
theorem closureFrame_continue_spec {m : Machine} {f : RubyCore.Frame}
    {Γb Γ : Env} {κb κ : Ctx} {Ib I τ : Ty}
    (lam : Bool) (brk : Option FrameId) (cl : Closure) (args : List Value)
    (ht : FirstOrder τ = true)
    (hf : ∀ a n, ResultOk (pushMethodFrame m f) Γb τ a n κb Ib →
      Framed m (popMethodFrame n))
    (hs : ∀ n v, ResultOk (pushMethodFrame m f) Γb τ (.val v) n κb Ib →
      StateOk κ Γ I (popMethodFrame n))
    {a : Answer} {n : Machine} (hr : ResultOk (pushMethodFrame m f) Γb τ a n κb Ib) :
    RunSpec m (deliverA a n [.blkFrameK m.frames.size lam brk cl args]) Γ τ κ I := by
  cases a with
  | val v =>
    apply RunSpec.step (by rfl) (step_blkFrameK_value n _ lam brk cl args v)
    exact RunSpec.answer ⟨hf _ _ hr,
      (denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) ht rfl).mp hr.2.1,
      fun _ _ => hs n v hr⟩
  | esc j =>
    apply blkFrameK_escape _ lam brk cl args j hr.2.1
    apply RunSpec.answer
    refine ⟨hf _ _ hr, ?_, fun _ hv => by cases hv⟩
    cases j <;> exact hr.2.1

theorem closureFrame_runSpec {m : Machine} {f : RubyCore.Frame} {e : Ratchet.Expr}
    {Γb Γ : Env} {κb κ : Ctx} {Ib I τ : Ty}
    (lam : Bool) (brk : Option FrameId) (cl : Closure) (args : List Value)
    (ht : FirstOrder τ = true)
    (hb : RunSpec (pushMethodFrame m f) (evalFrom (pushMethodFrame m f) e) Γb τ κb Ib)
    (hf : ∀ a n, ResultOk (pushMethodFrame m f) Γb τ a n κb Ib →
      Framed m (popMethodFrame n))
    (hs : ∀ n v, ResultOk (pushMethodFrame m f) Γb τ (.val v) n κb Ib →
      StateOk κ Γ I (popMethodFrame n)) :
    RunSpec m (pushK [.blkFrameK m.frames.size lam brk cl args]
      (evalFrom (pushMethodFrame m f) e)) Γ τ κ I := by
  apply hb.bindSpec (by
    intro k hk tag
    simp only [List.mem_singleton] at hk
    subst hk
    simp)
  intro a n hr
  exact closureFrame_continue_spec lam brk cl args ht hf hs hr

#print axioms blkFrameK_escape
#print axioms closureFrame_runSpec
end Ratchet.Denote.Typed
