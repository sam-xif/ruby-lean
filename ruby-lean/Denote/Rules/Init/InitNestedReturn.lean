import Denote.Rules.Init.InitReturn
import Denote.Rules.Method.MethodState

/-! A nested initializer returns within the same allocation anchor. Its caller's locals
survive when their types ignore mutable field snapshots; its receiver takes the new shape. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem InitFrame.pop {anchor : Heap} {m n : Machine} {f : RubyCore.Frame}
    (h : InitFrame anchor (pushMethodFrame m f) n)
    (hl : m.stack.headD 0 < m.frames.size) (hc : f.captured = none) :
    InitFrame anchor m (popMethodFrame n) :=
  ⟨h.growth, by simp [popMethodFrame, h.stack, pushMethodFrame],
    method_frame_pop hl hc h.stack h.frames, h.stable.reheap rfl rfl, h.phase⟩

theorem InitFrame.pop_currentFrame {anchor : Heap} {m n : Machine} {f : RubyCore.Frame}
    (h : InitFrame anchor (pushMethodFrame m f) n) (hl : FrameInRange m)
    (hc : f.captured = none) : (popMethodFrame n).currentFrame = m.currentFrame := by
  have hp := h.pop hl.2 hc
  rw [← rootFrame_eq_currentFrame (m := popMethodFrame n) (by rw [hp.stack]; exact hl.1),
    ← rootFrame_eq_currentFrame hl.1, hp.stack]
  exact method_frame_savedFrames hc h.frames _ hl.2

theorem InitFrame.body_self {anchor : Heap} {m n : Machine} {f : RubyCore.Frame}
    (h : InitFrame anchor (pushMethodFrame m f) n) : n.currentFrame.self = f.self := by
  have hs := h.frames.scope
  rw [rootFrame_eq_currentFrame (by simp [h.stack, pushMethodFrame]),
    rootFrame_eq_currentFrame (by simp [pushMethodFrame])] at hs
  simpa only [currentFrame_pushMethodFrame, frameScope] using congrArg FrameScope.self hs

theorem InitFrame.pop_env {anchor : Heap} {m n : Machine} {f : RubyCore.Frame} {Γ : Env}
    (h : InitFrame anchor (pushMethodFrame m f) n) (hl : FrameInRange m)
    (hu : RootUncaptured m) (hc : f.captured = none) (he : EnvOk Γ m)
    (ht : ∀ p ∈ Γ, IvarStable (stripAlias p.2) = true) : EnvOk Γ (popMethodFrame n) := by
  have hp := h.pop hl.2 hc
  have hpop := h.pop_currentFrame hl hc
  have hv (x : String) : (popMethodFrame n).getLocal x = m.getLocal x := by
    rw [getLocal_uncaptured (hp.frames.rootCaptured.trans hu), getLocal_uncaptured hu,
      rootFrame_eq_currentFrame (by rw [hp.stack]; exact hl.1), rootFrame_eq_currentFrame hl.1, hpop]
  refine ⟨?_, fun x hx => by rw [hv]; exact he.2 x hx⟩
  intro x τ hx
  obtain ⟨z, hz⟩ := envGet?_mem hx
  obtain ⟨hd, ha⟩ := he.1 x τ hx
  refine ⟨by rw [hv]; exact hp.stable _ (ht (z, τ) hz) _ hd, ?_⟩
  intro y ρ hy
  rw [hv, hv]
  exact ha y ρ hy

#print axioms InitFrame.pop
#print axioms InitFrame.pop_env
end Ratchet.Denote.Typed
