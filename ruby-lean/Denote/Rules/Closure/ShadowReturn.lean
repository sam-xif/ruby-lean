import Denote.Rules.Closure.ReadReturn

/-! Explicit parameters and block locals hide caller slots. Their final body types
describe the callee; the caller recovers its original values under those names. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem closure_shadowed_read {m n : Machine} {f : RubyCore.Frame}
    (hl : FrameInRange m) (hu : RootUncaptured m)
    (hc : f.captured = some (m.stack.headD 0))
    (h : Framed (pushMethodFrame m f) n) (x : String)
    (hx : f.locals.any (·.1 == x) = true)
    (hal : (m.frames.getD (m.stack.headD 0) default).localAlias = none)
    (hfa : f.localAlias = none) :
    (popMethodFrame n).getLocal x = m.getLocal x := by
  have he := h.frames.shadows x
    (by simpa [frameBinds, pushMethodFrame, Array.getD_eq_getD_getElem?] using hx)
    (m.stack.headD 0) (by simpa [pushMethodFrame] using Nat.lt_succ_of_lt hl.2)
    (by simpa [pushMethodFrame] using Nat.ne_of_lt hl.2)
  have hfind : (n.frames.getD (m.stack.headD 0) default).locals.find? (·.1 == x) =
      (m.frames.getD (m.stack.headD 0) default).locals.find? (·.1 == x) := by
    have hget (i : FrameId) (hi : i < m.frames.size) :
        (pushMethodFrame m f).frames.getD i default = m.frames.getD i default := by
      simp [pushMethodFrame, Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt]
    exact he.trans (congrArg (fun f => f.locals.find? (·.1 == x)) (hget _ hl.2))
  have hp := closure_pop_framed hl.2 hu hc h hal hfa
  rw [getLocal_uncaptured (hp.frames.rootCaptured.trans hu) x (hp.frames.rootAlias.trans hal),
    getLocal_uncaptured hu x hal]
  change (((n.frames.getD ((popMethodFrame n).stack.headD 0) default).locals.find?
    (·.1 == x)).map (·.2)).getD .nil = _
  rw [hp.stack, hfind]

#print axioms closure_shadowed_read
end Ratchet.Denote.Typed
