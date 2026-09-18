import Denote.Rules.Init.InitRun
import Denote.Rules.Method.MethodReturn

/-! Fresh initialization publishes the original caller's frame contract. The heap
anchor precedes allocation, while frame isolation is measured at method entry. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem initializer_pop_framed {m n : Machine} {f : RubyCore.Frame}
    (hl : m.stack.headD 0 < m.frames.size) (hc : f.captured = none)
    (hb : n.stack = (pushMethodFrame m f).stack)
    (hf : FramePres (pushMethodFrame m f) n) (hg : InitGrow m.heap n.heap) :
    Framed m (popMethodFrame n) :=
  Framed.of_initGrow hg (by simp [popMethodFrame, hb, pushMethodFrame])
    (method_frame_pop hl hc hb hf)

theorem InitFrame.publish {m n : Machine} {f : RubyCore.Frame}
    (hl : m.stack.headD 0 < m.frames.size) (hc : f.captured = none)
    (h : InitFrame m.heap (pushMethodFrame m f) n) : Framed m (popMethodFrame n) :=
  initializer_pop_framed hl hc h.stack h.frames h.growth

#print axioms initializer_pop_framed
end Ratchet.Denote.Typed
