import Denote.Rules.Iterator.FrameReturn

/-! A yielded block captures the caller below an ordinary method. It may update that
caller while preserving the suspended method's complete frame, including its locals.
Ordinary Framed at the method is too strong: its isolated clause forbids those writes. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

structure CallbackFramed (m n : Machine) : Prop where
  caller : Framed (popMethodFrame m) (popMethodFrame n)
  stack : n.stack = m.stack
  active : n.currentFrame = m.currentFrame
  bindings : ∀ x, frameBinds (popMethodFrame n) ((popMethodFrame n).stack.headD 0) x =
    frameBinds (popMethodFrame m) ((popMethodFrame m).stack.headD 0) x

theorem CallbackFramed.trans {m n out : Machine}
    (h : CallbackFramed m n) (h' : CallbackFramed n out) : CallbackFramed m out :=
  ⟨h.caller.trans h'.caller, h'.stack.trans h.stack, h'.active.trans h.active,
    fun x => (h'.bindings x).trans (h.bindings x)⟩

theorem CallbackFramed.reCtl {m n : Machine} (h : CallbackFramed m n) (c : Ctl) (K : List Kont) :
    CallbackFramed m (reCtl n c K) :=
  ⟨h.caller.trans (Framed_reCtl _ _ _), h.stack, h.active, h.bindings⟩

/-- The block's live capture chain skips the method. Consequently the method frame
is unchanged, while the outer caller receives the block's certified captured writes. -/
theorem callback_pop_framed {m n : Machine} {f : RubyCore.Frame}
    (hm : FrameInRange m) (hl : FrameInRange (popMethodFrame m))
    (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hu : RootUncaptured (popMethodFrame m))
    (hc : f.captured = some ((popMethodFrame m).stack.headD 0))
    (h : Framed (pushMethodFrame m f) n)
    (hal : (m.frames.getD ((popMethodFrame m).stack.headD 0) default).localAlias = none)
    (hfa : f.localAlias = none) : CallbackFramed m (popMethodFrame n) := by
  have hs : (popMethodFrame n).stack = m.stack := by
    simp [popMethodFrame, h.stack, pushMethodFrame]
  have hp := iterator_pop_framed hl.2 hu hc h hal hfa
  refine ⟨hp, hs, ?_, ?_⟩
  · rw [← rootFrame_eq_currentFrame (m := popMethodFrame n) (by rw [hs]; exact hm.1),
      ← rootFrame_eq_currentFrame hm.1, hs]
    exact closure_saved_frames_at (m := m) hl.2 hu hc h.frames _ hm.2 hne hal hfa
  · intro x
    change frameBinds n ((popMethodFrame (popMethodFrame n)).stack.headD 0) x = _
    rw [hp.stack]
    exact closure_saved_bindings h.frames _ hl.2 x

#print axioms callback_pop_framed
end Ratchet.Denote.Typed
