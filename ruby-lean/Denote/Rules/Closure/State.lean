import Denote.Rules.Closure.Environment
import Denote.Rules.Method.MethodState
import Denote.Sem.Closure.Scope

/-! Full conformance at required-positional closure entry. Runtime scope capabilities
for uncaptured activations are removed; captured lexical metadata and types are retained. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Full state transport consumes a separately proved complete body environment. This
allows closure-valued captures when their frame transport has been established. -/
theorem requiredClosureFrame_state_of_env {κ : Ctx} {Γ Γb : Env} {I : Ty}
    {m : Machine} {cl : Closure} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hscope : ClosureScopeEq m cl)
    (hlive : CaptureLive m cl.captured)
    (henv : EnvOk Γb (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)))
    (hk : ∀ x, constGet? (κ.withFrame none) x = constGet? κ x) :
    StateOk (κ.withoutRuntimeScope.withFrame none) Γb I
      (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) := by
  apply StateOk_captured_reframe
    (n := pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) hm ht ha rfl
  · simpa only [currentFrame_pushMethodFrame, requiredClosureFrame, Option.getD_none] using hscope.self
  · simpa only [currentFrame_pushMethodFrame, requiredClosureFrame] using hscope.block
  · simpa only [currentFrame_pushMethodFrame, requiredClosureFrame] using hscope.cref
  · simpa only [currentFrame_pushMethodFrame, requiredClosureFrame, Option.getD_none] using hscope.owner
  · exact hk
  · simp [FrameInRange, pushMethodFrame]
  · exact henv
  · simp [FrameOk, currentFrame_pushMethodFrame, requiredClosureFrame]
  · simp [currentFrame_pushMethodFrame, requiredClosureFrame]
  · simpa only [currentFrame_pushMethodFrame, requiredClosureFrame] using
      hlive.pushMethodFrame (requiredClosureFrame m cl (ps.map (·.1)) args)

theorem requiredClosureFrame_state {κ : Ctx} {Γ cap : Env} {I : Ty}
    {m : Machine} {cl : Closure} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hscope : ClosureScopeEq m cl) (hlive : CaptureLive m cl.captured)
    (hargs : DenAll (ps.map (·.2)) m args)
    (hcap : ∀ x τ, envGet? cap x = some τ → denM τ m (closLocal m cl x))
    (habs : ∀ x, envGet? cap x = none → closLocal m cl x = .nil)
    (htypes : ∀ p ∈ ps ++ blockLocals cl.locals ++ cap,
      FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (κ.withFrame none) x = constGet? κ x) :
    StateOk (κ.withoutRuntimeScope.withFrame none) (ps ++ blockLocals cl.locals ++ cap) I
      (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) :=
  requiredClosureFrame_state_of_env hm ht ha hscope hlive
    (requiredClosureFrame_envOk hargs hlive hcap habs htypes) hk

/-- The full state proof is attached to callClosure's actual next machine, including
its block continuation. Exact arity and lambda mode select this entry path. -/
theorem callClosure_required_state {κ : Ctx} {Γ cap : Env} {I : Ty}
    {m : Machine} {cl : Closure} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hscope : ClosureScopeEq m cl) (hlive : CaptureLive m cl.captured)
    (hargs : DenAll (ps.map (·.2)) m args)
    (hcap : ∀ x τ, envGet? cap x = some τ → denM τ m (closLocal m cl x))
    (habs : ∀ x, envGet? cap x = none → closLocal m cl x = .nil)
    (htypes : ∀ p ∈ ps ++ blockLocals cl.locals ++ cap,
      FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (κ.withFrame none) x = constGet? κ x)
    (hp : cl.params = (ps.map (·.1)).map RubyCore.Param.req) (hl : cl.lam = true)
    (hlen : args.length = ps.length) (brk : Option FrameId) :
    ∃ n, Interp.callClosure m cl args brk = .next n ∧
      StateOk (κ.withoutRuntimeScope.withFrame none) (ps ++ blockLocals cl.locals ++ cap) I n := by
  refine ⟨_, callClosure_required_lambda m cl (ps.map (·.1)) args brk none none hp hl
    (by simpa using hlen), ?_⟩
  exact StateOk_reCtl (requiredClosureFrame_state hm ht ha hscope hlive hargs hcap habs htypes hk) _ _

#print axioms requiredClosureFrame_state
#print axioms requiredClosureFrame_state_of_env
#print axioms callClosure_required_state
end Ratchet.Denote.Typed
