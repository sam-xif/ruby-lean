import RubyCore.Proof.RootFrameKont
import RubyCore.Proof.RootFrameEval

/-! The frame action follows the root execution through saved Enumerator callers. -/
set_option autoImplicit false
namespace RubyCore.Proof.Root
open Interp

theorem stepFn_frame_eq (K : List Kont) (hK : ContextFree K) (m : Machine)
    (hside : m.kont ≠ [] ∨ ∃ e, m.ctl = .eval e) :
    stepFn (pushRootK K m) = rootFrameR K (stepFn m) := by
  cases hc : m.ctl with
  | eval e => simp only [stepFn, pushRootK_ctl, hc, evalExpr_frame K hK]
  | send recv site name args blk kw =>
    simp only [stepFn, pushRootK_ctl, hc, invokeQueued_frame K hK]
  | value v =>
    have hne : m.kont ≠ [] := by
      rcases hside with hn | ⟨e, he⟩
      · exact hn
      · simp [hc] at he
    simp only [stepFn, pushRootK_ctl, hc, applyKont_frame K hK m v hne]
  | jump j =>
    have hne : m.kont ≠ [] := by
      rcases hside with hn | ⟨e, he⟩
      · exact hn
      · simp [hc] at he
    simp only [stepFn, pushRootK_ctl, hc, unwind_frame K hK m j hne]

theorem stepFn_frame (K : List Kont) (hK : ContextFree K) (m m₂ : Machine)
    (hside : m.kont ≠ [] ∨ ∃ e, m.ctl = .eval e)
    (h : stepFn m = .next m₂) :
    stepFn (pushRootK K m) = .next (pushRootK K m₂) := by
  rw [stepFn_frame_eq K hK m hside, h]
  rfl

#print axioms stepFn_frame
end RubyCore.Proof.Root
