import Denote.Rules.Closure.FrameReturn

/-! A body cannot shadow a previously unshadowed bound caller slot. Its final read of
that name is therefore the caller's outgoing read, including after captured writes. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem closure_bound_unshadowed_at {m n : Machine} {f : RubyCore.Frame} {root : FrameId}
    (hl : root < m.frames.size) (hu : (m.frames.getD root default).captured = none)
    (hc : f.captured = some root)
    (h : Framed (pushMethodFrame m f) n) (x : String)
    (hf : f.locals.any (·.1 == x) = false) (hx : frameBinds m root x = true) :
    frameBinds n (n.stack.headD 0) x = false := by
  let b := pushMethodFrame m f
  have hget (i : FrameId) (hi : i < m.frames.size) :
      b.frames.getD i default = m.frames.getD i default := by
    simp [b, pushMethodFrame, Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt]
  have hhead : b.frames.getD m.frames.size default = f := by
    simp [b, pushMethodFrame, Array.getD_eq_getD_getElem?]
  have hlive : CaptureLive b (some (b.stack.headD 0)) := by
    apply CaptureLive.frame (by simp [b, pushMethodFrame])
    change CaptureLive b (b.frames.getD m.frames.size default).captured
    rw [hhead, hc]
    exact CaptureLive.pushFrame (.frame hl (hu ▸ .none)) f
  apply h.frames.owners.unshadowed hlive h.stack x (fuel := 1) (by simp [pushMethodFrame])
  change Machine.setLocal.owner b x m.frames.size m.frames.size 2 ≠ m.frames.size
  rw [Machine.setLocal.owner, hhead]
  simp only [hf, Bool.false_eq_true, if_false, hc]
  rw [Machine.setLocal.owner, hget _ hl]
  change (if frameBinds m root x then root else _) ≠ m.frames.size
  rw [hx]
  exact Nat.ne_of_lt hl

theorem closure_bound_unshadowed {m n : Machine} {f : RubyCore.Frame}
    (hl : FrameInRange m) (hu : RootUncaptured m) (hc : f.captured = some (m.stack.headD 0))
    (h : Framed (pushMethodFrame m f) n) (x : String)
    (hf : f.locals.any (·.1 == x) = false) (hx : frameBinds m (m.stack.headD 0) x = true) :
    frameBinds n (n.stack.headD 0) x = false :=
  closure_bound_unshadowed_at hl.2 hu hc h x hf hx

theorem closure_bound_read {m n : Machine} {f : RubyCore.Frame}
    (hl : FrameInRange m) (hu : RootUncaptured m) (hc : f.captured = some (m.stack.headD 0))
    (h : Framed (pushMethodFrame m f) n) (x : String)
    (hf : f.locals.any (·.1 == x) = false) (hx : frameBinds m (m.stack.headD 0) x = true) :
    (popMethodFrame n).getLocal x = n.getLocal x := by
  have hs : (popMethodFrame n).stack = m.stack := by simp [popMethodFrame, h.stack, pushMethodFrame]
  have hp : (n.frames.getD (m.stack.headD 0) default).captured = none := by
    have he := congrArg RubyCore.Frame.captured (closure_saved_metadata h.frames _ hl.2)
    exact he.trans hu
  have hr : (n.frames.getD (n.stack.headD 0) default).captured = some (m.stack.headD 0) := by
    have he := h.frames.rootCaptured
    simpa [pushMethodFrame, Array.getD_eq_getD_getElem?, hc] using he
  have hn := find?_eq_none_of_any_false _ _ (closure_bound_unshadowed hl hu hc h x hf hx)
  have hz := h.frames.size
  simp only [pushMethodFrame, Array.size_push] at hz
  obtain ⟨k, hk⟩ : ∃ k, n.frames.size = k + 1 := ⟨n.frames.size - 1, by omega⟩
  have hpop : RootUncaptured (popMethodFrame n) := by
    change (n.frames.getD ((popMethodFrame n).stack.headD 0) default).captured = none
    rw [hs]
    exact hp
  rw [getLocal_uncaptured hpop, hs]
  change (((n.frames.getD (m.stack.headD 0) default).locals.find? (·.1 == x)).map (·.2)).getD .nil = _
  simp only [Machine.getLocal, hk, Machine.getLocal.go, hn, hr]
  cases he : (n.frames.getD (m.stack.headD 0) default).locals.find? (·.1 == x) with
  | none => simp only [hp, Option.map_none, Option.getD_none]
  | some p => cases p; rfl

#print axioms closure_bound_unshadowed
#print axioms closure_bound_read
end Ratchet.Denote.Typed
