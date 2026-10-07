import Books.TypeSoundness.Rules.Closure.EnvReturn
import Books.TypeSoundness.Rules.Closure.MainReturn

/-! Full main return with an outgoing environment computed from the body's types and
the caller's physical slots. No independent outgoing EnvOk premise remains. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem closure_projected_main_state {κ κb : Ctx} {Γ Γb : Env} {I Ib : Ty}
    {m n : Machine} {f : RubyCore.Frame} {names : List String}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hc : f.captured = some (m.stack.headD 0)) (hfa : f.localAlias = none)
    (hd : CaptureSlots names Γb m)
    (hf : ∀ x, frameBinds m (m.stack.headD 0) x = true → f.locals.any (·.1 == x) = false)
    (h : Framed (pushMethodFrame m f) n) (hn : StateOk κb Γb Ib n)
    (hmove : ∀ x τ, envGet? Γb x = some τ → names.contains x = true → ∀ v, denM (stripAlias τ) n v →
      denM (stripAlias τ) (popMethodFrame n) v) :
    StateOk (returnScopeCtx κ κb) (captureEnv names Γb) I (popMethodFrame n) := by
  have hu : RootUncaptured m := by
    rw [RootUncaptured, ← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime hr).captured
  exact closure_pop_main_state hm ht ha hr hw hcl hk hc hfa h
    (closure_projected_env hm.frameInRange hu hc hd hf h hn.env hm.localAlias hfa hmove) hn

theorem closure_projected_main_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty}
    {m : Machine} {f : RubyCore.Frame} {e : Checker.Expr} {names : List String}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hc : f.captured = some (m.stack.headD 0)) (hfa : f.localAlias = none)
    (hd : CaptureSlots names Γb m)
    (hf : ∀ x, frameBinds m (m.stack.headD 0) x = true → f.locals.any (·.1 == x) = false)
    (lam : Bool) (brk : Option FrameId) (cl : Closure) (args : List Value)
    (hτ : FirstOrder τ = true)
    (hb : RunSpec (pushMethodFrame m f) (evalFrom (pushMethodFrame m f) e) Γb τ κb Ib)
    (hmove : ∀ n, Framed (pushMethodFrame m f) n → ∀ x σ, envGet? Γb x = some σ →
      names.contains x = true → ∀ v, denM (stripAlias σ) n v → denM (stripAlias σ) (popMethodFrame n) v) :
    RunSpec m (pushK [.blkFrameK m.frames.size lam brk cl args]
      (evalFrom (pushMethodFrame m f) e)) (captureEnv names Γb) τ (returnScopeCtx κ κb) I := by
  apply closure_main_runSpec hm ht ha hr hw hcl hk hc lam brk cl args hτ hfa hb
  intro n v hn
  have hu : RootUncaptured m := by
    rw [RootUncaptured, ← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime hr).captured
  exact closure_projected_env hm.frameInRange hu hc hd hf hn.1 (hn.2.2 v rfl).env hm.localAlias hfa
    (hmove n hn.1)

#print axioms closure_projected_main_state
#print axioms closure_projected_main_runSpec
end Checker.Soundness.Typed
