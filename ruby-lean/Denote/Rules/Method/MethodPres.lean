import Denote.Rules.Method.Effects

/-! Mixed method effects retain callback identity and caller slot ownership. Method
locals may change, so these facts cannot be obtained from CallbackFramed.active. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem MethodEffects.callerInRange {m n : Machine} (h : MethodEffects m n)
    (hc : FrameInRange (popMethodFrame m)) : FrameInRange (popMethodFrame n) :=
  ⟨by simpa only [popMethodFrame, h.stack] using hc.1,
    by simpa only [popMethodFrame, h.stack] using Nat.lt_of_lt_of_le hc.2 h.size⟩

theorem MethodEffects.callerBindings {m n : Machine} (h : MethodEffects m n)
    (hc : FrameInRange (popMethodFrame m))
    (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0) (x : String) :
    frameBinds (popMethodFrame n) ((popMethodFrame n).stack.headD 0) x =
      frameBinds (popMethodFrame m) ((popMethodFrame m).stack.headD 0) x := by
  induction h with
  | ordinary h =>
    simpa only [frameBinds, popMethodFrame, h.stack] using h.frames.bindings.saved _ hc.2 (Ne.symm hne) x
  | callback h => exact h.bindings x
  | trans h _ ih ih' =>
    exact (ih' (h.callerInRange hc) (by simpa only [popMethodFrame, h.stack] using hne)).trans
      (ih hc hne)

theorem MethodEffects.callerScope {m n : Machine} (h : MethodEffects m n)
    (hc : FrameInRange (popMethodFrame m))
    (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0) :
    frameScope (popMethodFrame n).currentFrame = frameScope (popMethodFrame m).currentFrame := by
  induction h with
  | @ordinary m n h =>
    rw [← rootFrame_eq_currentFrame (m := popMethodFrame n) (by
        simpa only [popMethodFrame, h.stack] using hc.1), ← rootFrame_eq_currentFrame hc.1]
    have hs := congrArg frameScope (h.frames.saved _ hc.2 (Ne.symm hne))
    simpa only [frameScope, savedFrame, popMethodFrame, h.stack] using hs
  | @callback m n h =>
    rw [← rootFrame_eq_currentFrame (m := popMethodFrame n) (by rw [h.caller.stack]; exact hc.1),
      ← rootFrame_eq_currentFrame hc.1]
    exact h.caller.frames.scope
  | trans h _ ih ih' =>
    exact (ih' (h.callerInRange hc) (by simpa only [popMethodFrame, h.stack] using hne)).trans
      (ih hc hne)

theorem MethodEffects.methodScope {m n : Machine} (h : MethodEffects m n)
    (hm : FrameInRange m) (hc : FrameInRange (popMethodFrame m))
    (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hs : CallbackMethodScope m) : CallbackMethodScope n := by
  have ha := h.scope hm
  have hb := h.callerScope hc hne
  exact ⟨(congrArg FrameScope.self ha).trans (hs.self.trans (congrArg FrameScope.self hb).symm),
    (congrArg FrameScope.cref ha).trans (hs.cref.trans (congrArg FrameScope.cref hb).symm),
    (congrArg FrameScope.defmod ha).trans (hs.owner.trans (congrArg FrameScope.defmod hb).symm),
    (congrArg FrameScope.captured ha).trans hs.uncaptured,
    (congrArg FrameScope.localAlias ha).trans hs.unaliased⟩

theorem MethodEffects.proc {m n : Machine} {o : ObjId} {cl : Closure}
    (h : MethodEffects m n) (hp : (m.heap.get o).payload = .proc cl) :
    (n.heap.get o).payload = .proc cl := by
  have hv := h.procs.payload (.ref o) cl (by simp only [procClosure?, hp])
  cases he : (n.heap.get o).payload <;> simp_all [procClosure?]

theorem CallbackCaller.afterMethod {m n : Machine} {κ : Ctx} {Γ Γb : Env} {I : Ty}
    {cl : Closure} {ps : List SigParam} {names : List String}
    (hc : CallbackCaller κ Γ I cl ps names Γb m) (h : MethodEffects m n)
    (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hs : StateOk κ Γ I (popMethodFrame n)) : CallbackCaller κ Γ I cl ps names Γb n := by
  refine ⟨hs, ?_, ?_⟩
  · simpa only [popMethodFrame, h.stack] using hc.capture
  · intro x τ hx
    exact (h.callerBindings hc.state.frameInRange hne x).trans (hc.slots x τ hx)

#print axioms MethodEffects.callerBindings
#print axioms MethodEffects.methodScope
#print axioms CallbackCaller.afterMethod
end Ratchet.Denote.Typed
