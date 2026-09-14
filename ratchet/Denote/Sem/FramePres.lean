import Denote.Local

/-! Frame effects needed when a typed method returns to its caller. Ordinary method
activations have no captured frame, so local writes cannot touch their inactive callers.
Captured activations do not claim isolation: their writes may follow the captured chain.
-/

set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def RootUncaptured (m : Machine) : Prop :=
  (m.frames.getD (m.stack.headD 0) default).captured = none

structure FramePres (m n : Machine) : Prop where
  size : m.frames.size ≤ n.frames.size
  rootCaptured : (n.frames.getD (n.stack.headD 0) default).captured =
    (m.frames.getD (m.stack.headD 0) default).captured
  isolated : RootUncaptured m → ∀ i, i < m.frames.size → i ≠ m.stack.headD 0 →
    n.frames.getD i default = m.frames.getD i default

theorem FramePres.of_eq {m n : Machine} (hs : n.stack = m.stack)
    (hf : n.frames = m.frames) : FramePres m n := by
  refine ⟨by simp [hf], by rw [hf, hs], ?_⟩
  intro _ i _ _
  rw [hf]

theorem FramePres.refl (m : Machine) : FramePres m m := .of_eq rfl rfl

theorem FramePres.trans {m n p : Machine} (h : FramePres m n) (h' : FramePres n p)
    (hs : n.stack = m.stack) : FramePres m p := by
  refine ⟨Nat.le_trans h.size h'.size, h'.rootCaptured.trans h.rootCaptured, ?_⟩
  intro hc i hi hn
  have hc' : RootUncaptured n := h.rootCaptured.trans hc
  rw [h'.isolated hc' i (Nat.lt_of_lt_of_le hi h.size) (by simpa [hs] using hn),
    h.isolated hc i hi hn]

theorem FramePres.setLocal (m : Machine) (x : String) (v : Value) :
    FramePres m (m.setLocal x v) := by
  refine ⟨by simp, ?_, ?_⟩
  · simp only [setLocal_eq_setAt]
    exact setAt_captured _ _ _ _ _
  · intro hc i _ hn
    have ho : Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0)
        (m.frames.size + 1) = m.stack.headD 0 := by
      rw [Machine.setLocal.owner]
      split
      · rfl
      · unfold RootUncaptured at hc
        rw [hc]
    rw [setLocal_eq_setAt, ho]
    exact framesD_set!_ne _ _ _ _ hn

#print axioms FramePres.setLocal
end Ratchet.Denote
