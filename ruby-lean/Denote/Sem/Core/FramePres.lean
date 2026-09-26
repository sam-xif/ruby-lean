import Denote.Ty.Local
import Denote.Sem.Closure.CapturePath

/-! Frame effects needed when a typed method returns to its caller. Ordinary method
activations have no captured frame, so local writes cannot touch their inactive callers.
Captured activations may write locals along their captured chain. Saved metadata and
frames outside a live chain remain intact.
-/

set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def RootUncaptured (m : Machine) : Prop :=
  (m.frames.getD (m.stack.headD 0) default).captured = none

/-- The frame fields read by conformance. Locals, match state, and default visibility
are intentionally absent: evaluating a body may change those. -/
structure FrameScope where
  self : Value
  blk : Option Value
  cref : List ObjId
  defmod : ObjId
  captured : Option FrameId

def frameScope (f : RubyCore.Frame) : FrameScope :=
  ⟨f.self, f.blk, f.cref, f.defmod, f.captured⟩

/-- Saved activations may receive captured-local writes; all other fields stay intact. -/
def savedFrame (f : RubyCore.Frame) : RubyCore.Frame := { f with locals := [] }

structure FramePres (m n : Machine) : Prop where
  size : m.frames.size ≤ n.frames.size
  scope : frameScope (n.frames.getD (n.stack.headD 0) default) =
    frameScope (m.frames.getD (m.stack.headD 0) default)
  isolated : RootUncaptured m → ∀ i, i < m.frames.size → i ≠ m.stack.headD 0 →
    n.frames.getD i default = m.frames.getD i default
  saved : ∀ i, i < m.frames.size → i ≠ m.stack.headD 0 →
    savedFrame (n.frames.getD i default) = savedFrame (m.frames.getD i default)
  outside : CaptureLive m (some (m.stack.headD 0)) → ∀ i, i < m.frames.size →
    ¬ CapturePath m (some (m.stack.headD 0)) i →
      n.frames.getD i default = m.frames.getD i default

theorem FramePres.of_eq {m n : Machine} (hs : n.stack = m.stack)
    (hf : n.frames = m.frames) : FramePres m n := by
  exact ⟨by simp [hf], by rw [hf, hs], by intros; rw [hf],
    by intros; rw [hf], by intros; rw [hf]⟩

theorem FramePres.refl (m : Machine) : FramePres m m := .of_eq rfl rfl

theorem FramePres.rootCaptured {m n : Machine} (h : FramePres m n) :
    (n.frames.getD (n.stack.headD 0) default).captured =
      (m.frames.getD (m.stack.headD 0) default).captured :=
  congrArg FrameScope.captured h.scope

theorem FramePres.captured {m n : Machine} (h : FramePres m n) (hs : n.stack = m.stack)
    (i : FrameId) (hi : i < m.frames.size) :
    (n.frames.getD i default).captured = (m.frames.getD i default).captured := by
  by_cases he : i = m.stack.headD 0
  · subst i
    simpa only [hs] using h.rootCaptured
  · have hc := congrArg RubyCore.Frame.captured (h.saved i hi he)
    exact hc

theorem FramePres.trans {m n p : Machine} (h : FramePres m n) (h' : FramePres n p)
    (hs : n.stack = m.stack) : FramePres m p := by
  refine ⟨Nat.le_trans h.size h'.size, h'.scope.trans h.scope, ?_, ?_, ?_⟩
  · intro hc i hi hn
    have hc' : RootUncaptured n := h.rootCaptured.trans hc
    rw [h'.isolated hc' i (Nat.lt_of_lt_of_le hi h.size) (by simpa [hs] using hn),
      h.isolated hc i hi hn]
  · intro i hi hn
    exact (h'.saved i (Nat.lt_of_lt_of_le hi h.size) (by simpa [hs] using hn)).trans
      (h.saved i hi hn)
  · intro hl i hi hn
    have hl' : CaptureLive n (some (n.stack.headD 0)) := by
      rw [hs]
      exact hl.capture_preserved h.size (h.captured hs)
    rw [h'.outside hl' i (Nat.lt_of_lt_of_le hi h.size) (by
      rw [hs]; exact fun hp => hn ((CapturePath.preserved (h.captured hs) hl i).mp hp)),
      h.outside hl i hi hn]

theorem savedFrame_setAt (m : Machine) (x : String) (v : Value) (target i : FrameId) :
    savedFrame ((setAt m x v target).frames.getD i default) =
      savedFrame (m.frames.getD i default) := by
  by_cases he : i = target
  · subst i
    by_cases hi : target < m.frames.size
    · simp only [setAt, framesD_set!_self _ _ _ hi, setFrame, savedFrame]
    · rw [setAt, framesD_set!_oob _ _ _ hi]
  · rw [setAt, framesD_set!_ne _ _ _ _ he]

theorem FramePres.setLocal (m : Machine) (x : String) (v : Value) :
    FramePres m (m.setLocal x v) := by
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · simp only [setLocal_eq_setAt, setAt_stack, frameScope, setAt_self,
      setAt_blk, setAt_cref, setAt_defmod, setAt_captured]
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
  · intro i _ _
    rw [setLocal_eq_setAt]
    exact savedFrame_setAt m x v _ i
  · intro _ i _ hn
    rw [setLocal_eq_setAt]
    apply framesD_set!_ne
    intro he
    rcases setLocal_owner_path m x (m.stack.headD 0) (m.frames.size + 1)
      (m.stack.headD 0) with hr | hr
    · exact hn (he.symm ▸ hr.symm ▸ CapturePath.here _)
    · exact hn (he.symm ▸ hr)

#print axioms FramePres.setLocal
end Ratchet.Denote
