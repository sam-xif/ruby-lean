import Denote.Rules.Closure.FrameReturn

/-! An iterator activation is inert: its block captures the caller below it.
Project framing to that caller after popping both activations. Framing relative to
the iterator itself would incorrectly forbid writes to captured caller locals. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem iterator_frame_pop {m n : Machine} {f : RubyCore.Frame}
    (hl : (popMethodFrame m).stack.headD 0 < m.frames.size)
    (hu : RootUncaptured (popMethodFrame m))
    (hc : f.captured = some ((popMethodFrame m).stack.headD 0))
    (hb : n.stack = (pushMethodFrame m f).stack) (h : FramePres (pushMethodFrame m f) n)
    (hal : (m.frames.getD ((popMethodFrame m).stack.headD 0) default).localAlias = none)
    (hfa : f.localAlias = none) :
    FramePres (popMethodFrame m) (popMethodFrame (popMethodFrame n)) := by
  have hs : (popMethodFrame (popMethodFrame n)).stack = (popMethodFrame m).stack := by
    simp [popMethodFrame, hb, pushMethodFrame]
  have hf (i : FrameId) (hi : i < m.frames.size) (hne : i ≠ (popMethodFrame m).stack.headD 0) :=
    closure_saved_frames_at hl hu hc h i hi hne hal hfa
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
    · rw [hs]
      exact (congrArg RubyCore.Frame.captured (closure_saved_metadata h _ hl)).trans hu
    · rw [hs]
      exact (congrArg RubyCore.Frame.localAlias (closure_saved_metadata h _ hl)).trans hal

/-- The body's certified effects survive both pops, including caller-local writes.
The iterator's frame id may be old; each iteration need not allocate another one. -/
theorem iterator_pop_framed {m n : Machine} {f : RubyCore.Frame}
    (hl : (popMethodFrame m).stack.headD 0 < m.frames.size)
    (hu : RootUncaptured (popMethodFrame m))
    (hc : f.captured = some ((popMethodFrame m).stack.headD 0))
    (h : Framed (pushMethodFrame m f) n)
    (hal : (m.frames.getD ((popMethodFrame m).stack.headD 0) default).localAlias = none)
    (hfa : f.localAlias = none) :
    Framed (popMethodFrame m) (popMethodFrame (popMethodFrame n)) := by
  refine ⟨by simp [popMethodFrame, h.stack, pushMethodFrame], h.cls, h.nominal, ?_,
    iterator_frame_pop hl hu hc h.stack h.frames hal hfa, h.fields.reheap rfl rfl,
    h.cachedEigen, h.procs, h.phase, fun hr => h.rootClean hr⟩
  intro τ ht v hv
  have he : denM τ (pushMethodFrame m f) v :=
    (denM_heap_only (m₁ := popMethodFrame m) (m₂ := pushMethodFrame m f) ht rfl).mp hv
  exact (denM_heap_only (m₁ := n) (m₂ := popMethodFrame (popMethodFrame n)) ht rfl).mp
    (h.firstOrder τ ht v he)

theorem iterator_pop_metadata {m n : Machine} {f : RubyCore.Frame}
    (hl : FrameInRange (popMethodFrame m)) (h : Framed (pushMethodFrame m f) n) :
    savedFrame (popMethodFrame (popMethodFrame n)).currentFrame =
      savedFrame (popMethodFrame m).currentFrame := by
  have hs : (popMethodFrame (popMethodFrame n)).stack = (popMethodFrame m).stack := by
    simp [popMethodFrame, h.stack, pushMethodFrame]
  rw [← rootFrame_eq_currentFrame (m := popMethodFrame (popMethodFrame n))
      (by rw [hs]; exact hl.1), ← rootFrame_eq_currentFrame hl.1, hs]
  exact closure_saved_metadata h.frames _ hl.2

#print axioms iterator_pop_framed
#print axioms iterator_pop_metadata
end Ratchet.Denote.Typed
