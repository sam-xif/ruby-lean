import Ratchet.Guards.Callback
import Denote.Rules.Method.Callback

/-! Restore the active method's full state after a callback, including its actual block.
The captured caller supplies the updated heap world; the suspended method supplies its
unchanged locals and lexical scope. No callable arrow is used as a safety assumption. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

structure CallbackMethodScope (m : Machine) : Prop where
  self : m.currentFrame.self = (popMethodFrame m).currentFrame.self
  cref : m.currentFrame.cref = (popMethodFrame m).currentFrame.cref
  owner : m.currentFrame.defmod = (popMethodFrame m).currentFrame.defmod
  uncaptured : m.currentFrame.captured = none
  unaliased : m.currentFrame.localAlias = none

theorem callbackMethod_state {κ : Ctx} {Γ Γm : Env} {I : Ty} {m : Machine}
    {fr : Ratchet.Frame} {code : ClosureCode}
    (hm : StateOk κ Γ I (popMethodFrame m)) (hmain : closureMainB κ I = true)
    (hscope : CallbackMethodScope m) (hr : FrameInRange m)
    (he : EnvOk Γm m) (hf : FrameOk (some fr) m)
    (hb : BlockTyOk (some (.clos code .ivar0 .never)) m) :
    StateOk (callbackMethodCtx κ fr code) Γm I m := by
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain
  obtain ⟨_, _, _, hasm, hself, hblock, hconst, hi⟩ := hmain
  exact StateOk_reframe_block (n := m) (StateOk_withoutRuntimeScope hm)
    (ReframeFO.empty hi hself hblock hconst).withoutRuntimeScope hasm rfl
    hscope.self hb hscope.cref hscope.owner
    (by intro h; cases h) (by intro _ h; cases h) (by intro _ h; cases h)
    (fun x => (constGet?_empty (κ := κ.withoutRuntimeScope.withFrame (some fr)) hconst x).trans
      (constGet?_empty (κ := κ.withoutRuntimeScope) hconst x).symm) hr he hf hscope.unaliased
    (by rw [hscope.uncaptured]; exact .none) hm.rootClean

theorem CallbackFramed.inRange {m n : Machine} (h : CallbackFramed m n)
    (hm : FrameInRange m) : FrameInRange n :=
  ⟨by rw [h.stack]; exact hm.1,
    by rw [h.stack]; exact Nat.lt_of_lt_of_le hm.2 h.caller.frames.size⟩

theorem CallbackFramed.stable {m n : Machine} {τ : Ty} {v : Value}
    (h : CallbackFramed m n) (ht : activationStableB τ = true) (hv : denM τ m v) : denM τ n v :=
  activationStable_heap (m := popMethodFrame n) ht rfl
    (activationStable_framed ht h.caller (activationStable_heap (m := m) ht rfl hv))

theorem CallbackFramed.methodScope {m n : Machine} (h : CallbackFramed m n)
    (hl : FrameInRange (popMethodFrame m)) (hs : CallbackMethodScope m) : CallbackMethodScope n := by
  have hcaller := h.caller.frames.scope
  rw [rootFrame_eq_currentFrame (m := popMethodFrame n) (by rw [h.caller.stack]; exact hl.1),
    rootFrame_eq_currentFrame hl.1] at hcaller
  exact ⟨by rw [h.active]; exact hs.self.trans (congrArg FrameScope.self hcaller).symm,
    by rw [h.active]; exact hs.cref.trans (congrArg FrameScope.cref hcaller).symm,
    by rw [h.active]; exact hs.owner.trans (congrArg FrameScope.defmod hcaller).symm,
    by rw [h.active]; exact hs.uncaptured, by rw [h.active]; exact hs.unaliased⟩

/-- Callback effects restore the suspended method's ordinary expression context. Stable
local types include exact code-only closures (such as &b), as well as first-order values. -/
theorem CallbackResultOk.methodState {m n : Machine} {κ : Ctx} {Γ Γm : Env} {I ρ : Ty}
    {fr : Ratchet.Frame} {code : ClosureCode} {v : Value}
    (h : CallbackResultOk m Γ ρ κ I (.val v) n)
    (hc : StateOk κ Γ I (popMethodFrame m))
    (hm : StateOk (callbackMethodCtx κ fr code) Γm I m)
    (hmain : closureMainB κ I = true) (hs : CallbackMethodScope m)
    (ht : activationReturnB Γm = true) : StateOk (callbackMethodCtx κ fr code) Γm I n := by
  have hr := h.1.inRange hm.frameInRange
  have hu : RootUncaptured m := by
    rw [RootUncaptured, rootFrame_eq_currentFrame hm.frameInRange.1]
    exact hs.uncaptured
  apply callbackMethod_state (h.2.2 v rfl) hmain (h.1.methodScope hc.frameInRange hs) hr
  · exact hm.env.reframe_uncaptured hm.frameInRange hr hu h.1.active hm.localAlias
      (fun p hp _ hv => h.1.stable (List.all_eq_true.mp ht p hp) hv)
  · obtain ⟨hname, hrecv, hkind⟩ := hm.frame
    refine ⟨by rw [h.1.active]; exact hname, ?_, by rw [h.1.active]; exact hkind⟩
    rw [h.1.active]
    exact h.1.stable (by unfold activationStableB Frame.recvTy; split <;> rfl) hrecv
  · obtain ⟨b, hb, hd⟩ := hm.blockTy
    exact ⟨b, by rw [h.1.active]; exact hb, h.1.stable rfl hd⟩

#print axioms callbackMethod_state
#print axioms CallbackResultOk.methodState
end Ratchet.Denote.Typed
