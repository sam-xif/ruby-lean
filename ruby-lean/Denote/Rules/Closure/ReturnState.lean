import Denote.Rules.Closure.ReturnEnv
import Denote.Rules.Closure.MainReturn

/-! Full main-caller restoration with parameter/block-local shadowing. The return
environment is computed from the incoming caller and the outgoing body environments. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem closure_return_main_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty}
    {m : Machine} {f : RubyCore.Frame} {e : Ratchet.Expr} {shadow names : List String}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hc : f.captured = some (m.stack.headD 0))
    (hd : CaptureSlots names (withoutNames shadow Γb) m)
    (hf : ∀ x, f.locals.any (·.1 == x) = shadow.contains x)
    (lam : Bool) (brk : Option FrameId) (cl : Closure) (args : List Value)
    (hτ : FirstOrder τ = true)
    (hb : RunSpec (pushMethodFrame m f) (evalFrom (pushMethodFrame m f) e) Γb τ κb Ib)
    (hbefore : ∀ n, Framed (pushMethodFrame m f) n → ∀ x σ, envGet? Γ x = some σ →
      ∀ v, denM (stripAlias σ) m v → denM (stripAlias σ) (popMethodFrame n) v)
    (hafter : ∀ n, Framed (pushMethodFrame m f) n → ∀ x σ, envGet? Γb x = some σ →
      names.contains x = true → ∀ v, denM (stripAlias σ) n v →
        denM (stripAlias σ) (popMethodFrame n) v) :
    RunSpec m (pushK [.blkFrameK m.frames.size lam brk cl args]
      (evalFrom (pushMethodFrame m f) e)) (closureReturnEnv shadow names Γ Γb) τ
      (returnScopeCtx κ κb) I := by
  apply closure_main_runSpec hm ht ha hr hw hcl hk hc lam brk cl args hτ hb
  intro n v hn
  have hu : RootUncaptured m := by
    rw [RootUncaptured, ← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime hr).captured
  exact closure_return_env hm.frameInRange hu hc hd hf hn.1 hm.env
    (hn.2.2 v rfl).env (hbefore n hn.1) (hafter n hn.1)

#print axioms closure_return_main_runSpec
end Ratchet.Denote.Typed
