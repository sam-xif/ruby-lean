import Denote.Rules.Closure.FrameReturn

/-! A local already bound in the caller is written there by an unshadowing block frame.
Returning exposes the updated caller frame, not its pre-call local snapshot. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem captured_write_pop_frame {m : Machine} {f : RubyCore.Frame}
    (hl : FrameInRange m) (hc : f.captured = some (m.stack.headD 0)) (hf : f.locals = [])
    (x : String) (v : Value)
    (hx : (m.frames.getD (m.stack.headD 0) default).locals.any (·.1 == x) = true) :
    (popMethodFrame ((pushMethodFrame m f).setLocal x v)).currentFrame =
      (m.setLocal x v).currentFrame := by
  let b := pushMethodFrame m f
  have hbound : m.stack.headD 0 < m.frames.size := hl.2
  have hgetAll (i : FrameId) (hi : i < m.frames.size) :
      b.frames.getD i default = m.frames.getD i default := by
    simp [b, pushMethodFrame, Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt]
  have hget := hgetAll _ hbound
  have hhead : b.frames.getD m.frames.size default = f := by
    simp [b, pushMethodFrame, Array.getD_eq_getD_getElem?]
  have ho : Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0)
      (m.frames.size + 1) = m.stack.headD 0 := by rw [Machine.setLocal.owner, hx]; rfl
  have hob : Machine.setLocal.owner b x (b.stack.headD 0) (b.stack.headD 0)
      (b.frames.size + 1) = m.stack.headD 0 := by
    have hbs : b.stack.headD 0 = m.frames.size := rfl
    have hbsize : b.frames.size = m.frames.size + 1 := by simp [b, pushMethodFrame]
    rw [hbs, hbsize]
    rw [Machine.setLocal.owner, hhead]
    simp only [hf, List.any_nil, Bool.false_eq_true, if_false, hc]
    rw [Machine.setLocal.owner, hget, hx]
    rfl
  have hb : (b.setLocal x v).frames.getD (m.stack.headD 0) default =
      setFrame m x v (m.stack.headD 0) := by
    rw [setLocal_eq_setAt, hob, setAt,
      framesD_set!_self _ _ _ (by simpa [b, pushMethodFrame] using Nat.lt_succ_of_lt hl.2)]
    simp only [setFrame, hget]
  have hm : (m.setLocal x v).frames.getD (m.stack.headD 0) default =
      setFrame m x v (m.stack.headD 0) := by
    rw [setLocal_eq_setAt, ho, setAt, framesD_set!_self _ _ _ hl.2]
  rw [← rootFrame_eq_currentFrame (m := popMethodFrame (b.setLocal x v))
    (by simpa [popMethodFrame, b, pushMethodFrame] using hl.1),
    ← rootFrame_eq_currentFrame (m := m.setLocal x v) (by simpa using hl.1)]
  change (b.setLocal x v).frames.getD (m.stack.headD 0) default =
    (m.setLocal x v).frames.getD (m.stack.headD 0) default
  rw [hb, hm]

#print axioms captured_write_pop_frame
end Ratchet.Denote.Typed
