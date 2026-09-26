import Denote.Rules.Closure.Return
import Denote.Rules.Instance.MainReturn

/-! Restore full main-caller conformance from retained metadata and the body's heap world.
Captured writes require a separately proved outgoing caller environment. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem closure_pop_main_state {κ κb : Ctx} {Γ Γb Γout : Env} {I Ib : Ty}
    {m n : Machine} {f : RubyCore.Frame}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hc : f.captured = some (m.stack.headD 0))
    (h : Framed (pushMethodFrame m f) n) (he : EnvOk Γout (popMethodFrame n))
    (hn : StateOk κb Γb Ib n) : StateOk (returnScopeCtx κ κb) Γout I (popMethodFrame n) := by
  have hu : RootUncaptured m := by
    rw [RootUncaptured, ← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime hr).captured
  exact restore_main_state_of_metadata hm ht ha hr hw hcl hk
    (closure_pop_framed hm.frameInRange.2 hu hc h) (closure_pop_metadata hm.frameInRange h)
    he (h.phase.trans (hm.runtime hr).phase) hn

/-- The real block continuation now restores full caller state; only the outgoing
local environment must be supplied separately from the certified body result. -/
theorem closure_main_runSpec {κ κb : Ctx} {Γ Γb Γout : Env} {I Ib τ : Ty}
    {m : Machine} {f : RubyCore.Frame} {e : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hc : f.captured = some (m.stack.headD 0))
    (lam : Bool) (brk : Option FrameId) (cl : Closure) (args : List Value)
    (hτ : FirstOrder τ = true)
    (hb : RunSpec (pushMethodFrame m f) (evalFrom (pushMethodFrame m f) e) Γb τ κb Ib)
    (he : ∀ n v, ResultOk (pushMethodFrame m f) Γb τ (.val v) n κb Ib →
      EnvOk Γout (popMethodFrame n)) :
    RunSpec m (pushK [.blkFrameK m.frames.size lam brk cl args]
      (evalFrom (pushMethodFrame m f) e)) Γout τ (returnScopeCtx κ κb) I := by
  apply currentClosureFrame_runSpec hm.frameInRange.2 (by
    rw [RootUncaptured, ← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime hr).captured) hc lam brk cl args hτ hb
  intro n v hn
  exact closure_pop_main_state hm ht ha hr hw hcl hk hc hn.1 (he n v hn) (hn.2.2 v rfl)

#print axioms closure_pop_main_state
#print axioms closure_main_runSpec
end Ratchet.Denote.Typed
