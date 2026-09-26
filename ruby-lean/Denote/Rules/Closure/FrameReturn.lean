import Denote.Rules.Closure.Entry
import Denote.Rules.Method.MethodState

/-! Return framing for a closure capturing its uncaptured caller. Local writes may
reach that caller; other old frames and every saved activation's metadata survive. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem closure_saved_metadata {m n : Machine} {f : RubyCore.Frame}
    (h : FramePres (pushMethodFrame m f) n) (i : FrameId) (hi : i < m.frames.size) :
    savedFrame (n.frames.getD i default) = savedFrame (m.frames.getD i default) := by
  have hs := h.saved i (by simpa [pushMethodFrame] using Nat.lt_succ_of_lt hi)
    (by simpa [pushMethodFrame] using Nat.ne_of_lt hi)
  simpa [pushMethodFrame, Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt] using hs

theorem closure_saved_bindings {m n : Machine} {f : RubyCore.Frame}
    (h : FramePres (pushMethodFrame m f) n) (i : FrameId) (hi : i < m.frames.size) (x : String) :
    frameBinds n i x = frameBinds m i x := by
  have hs := h.bindings.saved i (by simpa [pushMethodFrame] using Nat.lt_succ_of_lt hi)
    (by simpa [pushMethodFrame] using Nat.ne_of_lt hi) x
  simpa [frameBinds, pushMethodFrame, Array.getD, hi, Nat.lt_succ_of_lt hi,
    Array.getElem_push_lt] using hs

/-- A block can skip an inert iterator activation and capture an older caller.
Only that captured caller may change; the argument does not require it to be active. -/
theorem closure_saved_frames_at {m n : Machine} {f : RubyCore.Frame} {root : FrameId}
    (hl : root < m.frames.size) (hu : (m.frames.getD root default).captured = none)
    (hc : f.captured = some root) (h : FramePres (pushMethodFrame m f) n)
    (i : FrameId) (hi : i < m.frames.size) (hne : i ≠ root) :
    n.frames.getD i default = m.frames.getD i default := by
  let b := pushMethodFrame m f
  have hget (j : FrameId) (hj : j < m.frames.size) :
      b.frames.getD j default = m.frames.getD j default := by
    simp [b, pushMethodFrame, Array.getD, hj, Nat.lt_succ_of_lt hj, Array.getElem_push_lt]
  have hhead : b.frames.getD m.frames.size default = f := by
    simp [b, pushMethodFrame, Array.getD_eq_getD_getElem?]
  have hparent : CaptureLive m (some root) := .frame hl (hu ▸ .none)
  have hbody : CaptureLive b (some (b.stack.headD 0)) := by
    apply CaptureLive.frame (by simp [b, pushMethodFrame])
    change CaptureLive b (b.frames.getD m.frames.size default).captured
    rw [hhead, hc]
    exact CaptureLive.pushFrame hparent f
  have hout : ¬ CapturePath b (some (b.stack.headD 0)) i := by
    intro hp
    change CapturePath b (some m.frames.size) i at hp
    have hsplit : i = m.frames.size ∨
        CapturePath b (b.frames.getD m.frames.size default).captured i := by
      cases hp with
      | here => exact Or.inl rfl
      | next hp => exact Or.inr hp
    rcases hsplit with he | hp
    · exact (Nat.ne_of_lt hi) he
    ·
      rw [hhead, hc] at hp
      exact hne (hp.uncaptured (by rw [hget _ hl]; exact hu))
  exact (h.outside hbody i (by simpa [b, pushMethodFrame] using Nat.lt_succ_of_lt hi) hout).trans
    (hget i hi)

theorem closure_saved_frames {m n : Machine} {f : RubyCore.Frame}
    (hl : m.stack.headD 0 < m.frames.size) (hu : RootUncaptured m)
    (hc : f.captured = some (m.stack.headD 0)) (h : FramePres (pushMethodFrame m f) n)
    (i : FrameId) (hi : i < m.frames.size) (hne : i ≠ m.stack.headD 0) :
    n.frames.getD i default = m.frames.getD i default :=
  closure_saved_frames_at hl hu hc h i hi hne

theorem closure_frame_pop {m n : Machine} {f : RubyCore.Frame}
    (hl : m.stack.headD 0 < m.frames.size) (hu : RootUncaptured m)
    (hc : f.captured = some (m.stack.headD 0))
    (hb : n.stack = (pushMethodFrame m f).stack) (h : FramePres (pushMethodFrame m f) n) :
    FramePres m (popMethodFrame n) := by
  have hs : (popMethodFrame n).stack = m.stack := by simp [popMethodFrame, hb, pushMethodFrame]
  have hf := closure_saved_frames hl hu hc h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, .of_frames hf⟩
  · have hh := h.size
    simp only [pushMethodFrame, Array.size_push] at hh
    exact Nat.le_trans (Nat.le_succ _) hh
  · rw [hs]
    have he := congrArg frameScope (closure_saved_metadata h _ hl)
    exact he
  · intro _ i hi hn; exact hf i hi hn
  · intro i hi hn; exact congrArg savedFrame (hf i hi hn)
  · intro _ i hi hn
    exact hf i hi (by intro he; subst i; exact hn (.here _))
  · exact ⟨fun i hi x hx => (closure_saved_bindings h i hi x).trans hx,
      fun i hi _ x => closure_saved_bindings h i hi x⟩
  · apply OwnersPres.uncaptured hs hu
    rw [hs]
    have he := congrArg RubyCore.Frame.captured (closure_saved_metadata h _ hl)
    exact he.trans hu

theorem closure_pop_framed {m n : Machine} {f : RubyCore.Frame}
    (hl : m.stack.headD 0 < m.frames.size) (hu : RootUncaptured m)
    (hc : f.captured = some (m.stack.headD 0))
    (h : Framed (pushMethodFrame m f) n) : Framed m (popMethodFrame n) := by
  refine ⟨by simp [popMethodFrame, h.stack, pushMethodFrame], h.cls, h.nominal, ?_,
    closure_frame_pop hl hu hc h.stack h.frames, h.fields.reheap rfl rfl, h.cachedEigen, h.procs, h.phase⟩
  intro τ ht v hv
  have he : denM τ (pushMethodFrame m f) v :=
    (denM_heap_only (m₁ := m) (m₂ := pushMethodFrame m f) ht rfl).mp hv
  exact (denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) ht rfl).mp (h.firstOrder τ ht v he)

theorem closure_pop_metadata {m n : Machine} {f : RubyCore.Frame}
    (hl : FrameInRange m) (h : Framed (pushMethodFrame m f) n) :
    savedFrame (popMethodFrame n).currentFrame = savedFrame m.currentFrame := by
  have hs : (popMethodFrame n).stack = m.stack := by simp [popMethodFrame, h.stack, pushMethodFrame]
  rw [← rootFrame_eq_currentFrame (m := popMethodFrame n) (by rw [hs]; exact hl.1),
    ← rootFrame_eq_currentFrame hl.1, hs]
  exact closure_saved_metadata h.frames _ hl.2

#print axioms closure_saved_frames
#print axioms closure_saved_bindings
#print axioms closure_pop_framed
#print axioms closure_pop_metadata
end Ratchet.Denote.Typed
