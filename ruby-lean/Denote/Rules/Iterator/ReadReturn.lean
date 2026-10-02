import Denote.Rules.Iterator.FrameReturn
import Denote.Rules.Closure.ReadReturn

/-! Recover caller reads past the inert iterator. Parameters preserve hidden caller
values; unshadowed bound captures follow the body; absent caller slots stay nil. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem iterator_bound_read {m n : Machine} {f : RubyCore.Frame}
    (hl : FrameInRange (popMethodFrame m)) (hu : RootUncaptured (popMethodFrame m))
    (hc : f.captured = some ((popMethodFrame m).stack.headD 0))
    (h : Framed (pushMethodFrame m f) n) (x : String)
    (hf : f.locals.any (·.1 == x) = false)
    (hx : frameBinds (popMethodFrame m) ((popMethodFrame m).stack.headD 0) x = true)
    (hal : (m.frames.getD ((popMethodFrame m).stack.headD 0) default).localAlias = none)
    (hfa : f.localAlias = none) :
    (popMethodFrame (popMethodFrame n)).getLocal x = n.getLocal x := by
  have hp := iterator_pop_framed hl.2 hu hc h hal hfa
  have hpa : (n.frames.getD ((popMethodFrame m).stack.headD 0) default).localAlias = none :=
    (congrArg RubyCore.Frame.localAlias (closure_saved_metadata h.frames _ hl.2)).trans hal
  have hna : (n.frames.getD (n.stack.headD 0) default).localAlias = none := by
    rw [h.frames.rootAlias]
    simpa [pushMethodFrame, Array.getD_eq_getD_getElem?] using hfa
  have hcap : (n.frames.getD ((popMethodFrame m).stack.headD 0) default).captured = none := by
    have he := congrArg RubyCore.Frame.captured (closure_saved_metadata h.frames _ hl.2)
    exact he.trans hu
  have hr : (n.frames.getD (n.stack.headD 0) default).captured =
      some ((popMethodFrame m).stack.headD 0) := by
    have he := h.frames.rootCaptured
    simpa [pushMethodFrame, Array.getD_eq_getD_getElem?, hc] using he
  have hn := find?_eq_none_of_any_false _ _
    (closure_bound_unshadowed_at (m := m) hl.2 hu hc h x hf hx hal hfa)
  have hz := h.frames.size
  simp only [pushMethodFrame, Array.size_push] at hz
  obtain ⟨k, hk⟩ : ∃ k, n.frames.size = k + 1 := ⟨n.frames.size - 1, by omega⟩
  rw [getLocal_uncaptured (hp.frames.rootCaptured.trans hu) x
    (by rw [hp.stack]; exact hpa), hp.stack]
  change (((n.frames.getD ((popMethodFrame m).stack.headD 0) default).locals.find?
    (·.1 == x)).map (·.2)).getD .nil = _
  simp only [Machine.getLocal, hk, Machine.getLocal.go, localFrameId_of_noAlias hna,
    localFrameId_of_noAlias (m := n) hpa, hn, hr]
  cases he : (n.frames.getD ((popMethodFrame m).stack.headD 0) default).locals.find? (·.1 == x) with
  | none => simp only [hcap, Option.map_none, Option.getD_none]
  | some p => cases p; rfl

theorem iterator_shadowed_read {m n : Machine} {f : RubyCore.Frame}
    (hl : FrameInRange (popMethodFrame m)) (hu : RootUncaptured (popMethodFrame m))
    (hc : f.captured = some ((popMethodFrame m).stack.headD 0))
    (h : Framed (pushMethodFrame m f) n) (x : String)
    (hx : f.locals.any (·.1 == x) = true)
    (hal : (m.frames.getD ((popMethodFrame m).stack.headD 0) default).localAlias = none)
    (hfa : f.localAlias = none) :
    (popMethodFrame (popMethodFrame n)).getLocal x = (popMethodFrame m).getLocal x := by
  have he := h.frames.shadows x
    (by simpa [frameBinds, pushMethodFrame, Array.getD_eq_getD_getElem?] using hx)
    ((popMethodFrame m).stack.headD 0) (by simpa [pushMethodFrame, popMethodFrame] using Nat.lt_succ_of_lt hl.2)
    (by simpa [pushMethodFrame, popMethodFrame] using Nat.ne_of_lt hl.2)
  have hfind : (n.frames.getD ((popMethodFrame m).stack.headD 0) default).locals.find? (·.1 == x) =
      (m.frames.getD ((popMethodFrame m).stack.headD 0) default).locals.find? (·.1 == x) := by
    have hget (i : FrameId) (hi : i < m.frames.size) :
        (pushMethodFrame m f).frames.getD i default = m.frames.getD i default := by
      simp [pushMethodFrame, Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt]
    exact he.trans (congrArg (fun f => f.locals.find? (·.1 == x)) (hget _ hl.2))
  have hp := iterator_pop_framed hl.2 hu hc h hal hfa
  rw [getLocal_uncaptured (hp.frames.rootCaptured.trans hu) x (hp.frames.rootAlias.trans hal),
    getLocal_uncaptured hu x hal]
  change (((n.frames.getD ((popMethodFrame (popMethodFrame n)).stack.headD 0) default).locals.find?
    (·.1 == x)).map (·.2)).getD .nil = _
  rw [hp.stack, hfind]
  rfl

theorem iterator_absent_read {m n : Machine} {f : RubyCore.Frame}
    (hl : FrameInRange (popMethodFrame m)) (hu : RootUncaptured (popMethodFrame m))
    (h : Framed (pushMethodFrame m f) n) (x : String)
    (hx : frameBinds (popMethodFrame m) ((popMethodFrame m).stack.headD 0) x = false)
    (hal : (m.frames.getD ((popMethodFrame m).stack.headD 0) default).localAlias = none) :
    (popMethodFrame (popMethodFrame n)).getLocal x = .nil := by
  have hs : (popMethodFrame (popMethodFrame n)).stack = (popMethodFrame m).stack := by
    simp [popMethodFrame, h.stack, pushMethodFrame]
  have hc : RootUncaptured (popMethodFrame (popMethodFrame n)) := by
    change (n.frames.getD ((popMethodFrame (popMethodFrame n)).stack.headD 0) default).captured = none
    rw [hs]
    have he := congrArg RubyCore.Frame.captured (closure_saved_metadata h.frames _ hl.2)
    exact he.trans hu
  have hb := (closure_saved_bindings h.frames _ hl.2 x).trans hx
  have hf := find?_eq_none_of_any_false _ _ hb
  rw [getLocal_uncaptured hc x (by
    rw [hs]
    exact (congrArg RubyCore.Frame.localAlias (closure_saved_metadata h.frames _ hl.2)).trans hal), hs]
  change (((n.frames.getD ((popMethodFrame m).stack.headD 0) default).locals.find?
    (·.1 == x)).map (·.2)).getD .nil = _
  rw [hf]; rfl

#print axioms iterator_bound_read
#print axioms iterator_shadowed_read
#print axioms iterator_absent_read
end Ratchet.Denote.Typed
