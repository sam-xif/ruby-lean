import Books.TypeSoundness.Rules.Closure.State

/-! A closure capturing the current uncaptured activation gets complete capture facts
from the caller's environment. Value transport remains explicit, including nested closures. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem currentClosureFrame_envOk {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {cl : Closure} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (hu : m.currentFrame.captured = none)
    (hc : cl.captured = some (m.stack.headD 0))
    (hargs : DenAll (ps.map (·.2)) m args)
    (htypes : ∀ p ∈ ps ++ blockLocals cl.locals ++ Γ, isAliasTy p.2 = false)
    (hmove : ∀ p ∈ ps ++ blockLocals cl.locals ++ Γ, ∀ v, denM p.2 m v →
      denM p.2 (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) v) :
    EnvOk (ps ++ blockLocals cl.locals ++ Γ)
      (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) := by
  have hlive : CaptureLive m cl.captured := by rw [hc]; exact hm.toStateCore.captureLive
  apply requiredClosureFrame_envOk_of_transport hargs (cap := Γ)
  · exact hlive
  · intro x τ hx
    obtain ⟨z, hz⟩ := envGet?_mem hx
    have ht := htypes (z, τ) (List.mem_append_right _ hz)
    have hs : stripAlias τ = τ := by cases τ <;> simp_all [stripAlias, isAliasTy]
    rw [closLocal_current hc hlive]
    simpa only [hs] using (hm.env.1 x τ hx).1
  · intro x hx
    rw [closLocal_current hc hlive]
    exact hm.env.2 x hx
  · exact htypes
  · exact hmove

/-- Actual required-lambda entry from a complete caller environment. The capture points
to that caller; arbitrary older/escaped captures need their own scope and environment facts. -/
theorem callClosure_current_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {cl : Closure} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hu : m.currentFrame.captured = none) (hc : cl.captured = some (m.stack.headD 0))
    (hargs : DenAll (ps.map (·.2)) m args)
    (htypes : ∀ p ∈ ps ++ blockLocals cl.locals ++ Γ, isAliasTy p.2 = false)
    (hmove : ∀ p ∈ ps ++ blockLocals cl.locals ++ Γ, ∀ v, denM p.2 m v →
      denM p.2 (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) v)
    (hk : ∀ x, constGet? (κ.withFrame none) x = constGet? κ x)
    (hp : cl.params = (ps.map (·.1)).map RubyCore.Param.req) (hl : cl.lam = true)
    (hlen : args.length = ps.length) (brk : Option FrameId)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none) :
    ∃ n, Interp.callClosure m cl args brk = .next n ∧
      StateOk (κ.withoutRuntimeScope.withFrame none) (ps ++ blockLocals cl.locals ++ Γ) I n := by
  refine ⟨_, callClosure_required_lambda m cl (ps.map (·.1)) args brk none none hp hl
    (by simpa using hlen) henum hfor, ?_⟩
  exact StateOk_reCtl (requiredClosureFrame_state_of_env hm ht ha
    (ClosureScopeEq.current hm.frameInRange hc)
    (by rw [hc]; exact hm.toStateCore.captureLive)
    (currentClosureFrame_envOk hm hu hc hargs htypes hmove) hk) _ _

#print axioms currentClosureFrame_envOk
#print axioms callClosure_current_state
end Checker.Soundness.Typed
