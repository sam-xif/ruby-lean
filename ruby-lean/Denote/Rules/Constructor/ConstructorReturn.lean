import Denote.Rules.Constructor.ConstructorState
import Denote.Rules.Init.InitReturn
import Denote.Rules.Instance.MainReturn

/-! Publish the initialized receiver while restoring the original caller. Heap growth
is anchored before allocation; frame isolation is measured at initializer entry. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem constructor_frame_pres {m n : Machine} {k : ObjId} {md : MethodDef}
    {ps : List SigParam} {args : List Value}
    (h : InitFrame m.heap (constructorFrame m k md ps args) n) :
    FramePres (pushMethodFrame m
      (requiredFrame (.ref m.heap.objs.size) "initialize" md (ps.map (·.1)) args)) n :=
  ⟨h.frames.size, h.frames.scope, h.frames.isolated⟩

theorem constructor_pop_framed {m n : Machine} {k : ObjId} {md : MethodDef}
    {ps : List SigParam} {args : List Value} (hl : FrameInRange m)
    (h : InitFrame m.heap (constructorFrame m k md ps args) n) : Framed m (popMethodFrame n) :=
  initializer_pop_framed hl.2 rfl h.stack (constructor_frame_pres h) h.growth

theorem constructor_pop_currentFrame {m n : Machine} {k : ObjId} {md : MethodDef}
    {ps : List SigParam} {args : List Value} (hl : FrameInRange m)
    (h : InitFrame m.heap (constructorFrame m k md ps args) n) :
    (popMethodFrame n).currentFrame = m.currentFrame := by
  have hp := constructor_pop_framed hl h
  rw [← rootFrame_eq_currentFrame (m := popMethodFrame n) (by rw [hp.stack]; exact hl.1),
    ← rootFrame_eq_currentFrame hl.1, hp.stack]
  exact method_frame_savedFrames rfl (constructor_frame_pres h) _ hl.2

theorem constructor_pop_env {m n : Machine} {k : ObjId} {md : MethodDef}
    {ps : List SigParam} {args : List Value} {Γ : Env} (hl : FrameInRange m)
    (hu : RootUncaptured m) (he : EnvOk Γ m)
    (ht : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (h : InitFrame m.heap (constructorFrame m k md ps args) n) :
    EnvOk Γ (popMethodFrame n) := by
  have hp := constructor_pop_framed hl h
  have hpop := constructor_pop_currentFrame hl h
  have hv (x : String) : (popMethodFrame n).getLocal x = m.getLocal x := by
    rw [getLocal_uncaptured (hp.frames.rootCaptured.trans hu), getLocal_uncaptured hu,
      rootFrame_eq_currentFrame (by rw [hp.stack]; exact hl.1), rootFrame_eq_currentFrame hl.1, hpop]
  refine ⟨?_, fun x hx => by rw [hv]; exact he.2 x hx⟩
  intro x τ hx
  obtain ⟨z, hz⟩ := envGet?_mem hx
  obtain ⟨hd, ha⟩ := he.1 x τ hx
  refine ⟨by rw [hv]; exact hp.firstOrder _ (ht (z, τ) hz) _ hd, ?_⟩
  intro y ρ hy
  rw [hv, hv]
  exact ha y ρ hy

theorem constructor_body_self {m n : Machine} {k : ObjId} {md : MethodDef}
    {ps : List SigParam} {args : List Value}
    (h : InitFrame m.heap (constructorFrame m k md ps args) n) :
    n.currentFrame.self = .ref m.heap.objs.size := by
  have hs := h.frames.scope
  rw [rootFrame_eq_currentFrame (by simp [h.stack, constructorFrame, pushMethodFrame]),
    rootFrame_eq_currentFrame (by simp [constructorFrame, pushMethodFrame])] at hs
  simpa only [constructorFrame, currentFrame_pushMethodFrame, requiredFrame, frameScope] using
    congrArg FrameScope.self hs

theorem constructor_result {κb : Ctx} {Γb : Env} {Ib : Ty} {m n : Machine}
    {cn : String} {k : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    (h : InitFrame m.heap (constructorFrame m k md ps args) n)
    (hn : StateOk κb Γb Ib n) (hs : κb.selfTy = some (.inst cn .ivar0))
    (hi : FirstOrder Ib = true) :
    denM (.inst cn Ib) (popMethodFrame n) (.ref m.heap.objs.size) := by
  have hv := hn.selfTy
  simp only [SelfTyOk, hs] at hv
  rw [denM] at hv
  have hinst : denM (.inst cn Ib) n n.currentFrame.self := by
    rw [denM]
    exact ⟨hv.1, hn.selfSpine.1⟩
  rw [constructor_body_self h] at hinst
  exact (denM_heap_only (τ := .inst cn Ib) (m₁ := n) (m₂ := popMethodFrame n) hi rfl).mp hinst

theorem constructor_pop_main_state {κ κb : Ctx} {Γ Γb : Env} {I Ib : Ty} {m n : Machine}
    {cn : String} {k : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hq : κb.scope.runtimeClass = some cn)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (h : InitFrame m.heap (constructorFrame m k md ps args) n)
    (hn : StateOk κb Γb Ib n) : StateOk (returnScopeCtx κ κb) Γ I (popMethodFrame n) := by
  have hu : RootUncaptured m := by
    unfold RootUncaptured
    rw [rootFrame_eq_currentFrame hm.frameInRange.1]
    exact (hm.runtime hr).captured
  obtain ⟨_, scope⟩ := hn.classRuntime cn hq
  exact restore_main_state hm ht ha hr hw hcl hk (constructor_pop_framed hm.frameInRange h)
    (constructor_pop_currentFrame hm.frameInRange h) (constructor_pop_env hm.frameInRange hu hm.env hΓ h)
    scope.phase hn

#print axioms constructor_result
#print axioms constructor_pop_main_state
end Ratchet.Denote.Typed
