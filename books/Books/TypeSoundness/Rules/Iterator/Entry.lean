import Books.TypeSoundness.Rules.Closure.Current

/-! The active iterator is inert; argument and capture types come from its caller.
The actual block frame still sits above that iterator and captures the caller below it. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem iteratorClosureFrame_envOk {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {cl : Closure} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I (popMethodFrame m)) (hu : (popMethodFrame m).currentFrame.captured = none)
    (hc : cl.captured = some ((popMethodFrame m).stack.headD 0))
    (hargs : DenAll (ps.map (·.2)) (popMethodFrame m) args)
    (htypes : ∀ p ∈ ps ++ blockLocals cl.locals ++ Γ, isAliasTy p.2 = false)
    (hmove : ∀ p ∈ ps ++ blockLocals cl.locals ++ Γ, ∀ v, denM p.2 (popMethodFrame m) v →
      denM p.2 (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) v) :
    EnvOk (ps ++ blockLocals cl.locals ++ Γ)
      (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) := by
  have hlive : CaptureLive (popMethodFrame m) cl.captured := by
    rw [hc]; exact hm.toStateCore.captureLive
  have hread : closLocal m cl = (popMethodFrame m).getLocal := by
    rw [← closLocal_current hc hlive]
    funext x
    simp only [closLocal, hc, frameLocal?, frameLocal]
    exact frameLocal_go_preserved (m := popMethodFrame m) (n := m) (fun _ _ => rfl)
      x _ _ (hc ▸ hlive)
  apply requiredClosureFrame_envOk_from hargs (cap := Γ)
  · exact CaptureLive.frames_preserved (m := popMethodFrame m) (n := m)
      (Nat.le_refl _) (fun _ _ => rfl) hlive
  · intro x τ hx
    obtain ⟨z, hz⟩ := envGet?_mem hx
    have ht := htypes (z, τ) (List.mem_append_right _ hz)
    have hs : stripAlias τ = τ := by cases τ <;> simp_all [stripAlias, isAliasTy]
    rw [hread]
    simpa only [hs] using (hm.env.1 x τ hx).1
  · intro x hx
    rw [hread]
    exact hm.env.2 x hx
  · exact htypes
  · exact hmove

theorem iteratorClosureFrame_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {cl : Closure} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I (popMethodFrame m)) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hu : (popMethodFrame m).currentFrame.captured = none)
    (hc : cl.captured = some ((popMethodFrame m).stack.headD 0))
    (hargs : DenAll (ps.map (·.2)) (popMethodFrame m) args)
    (htypes : ∀ p ∈ ps ++ blockLocals cl.locals ++ Γ, isAliasTy p.2 = false)
    (hmove : ∀ p ∈ ps ++ blockLocals cl.locals ++ Γ, ∀ v, denM p.2 (popMethodFrame m) v →
      denM p.2 (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) v)
    (hk : ∀ x, constGet? (κ.withFrame none) x = constGet? κ x) :
    StateOk (κ.withoutRuntimeScope.withFrame none) (ps ++ blockLocals cl.locals ++ Γ) I
      (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) := by
  have scope := ClosureScopeEq.current hm.frameInRange hc
  apply StateOk_captured_reframe
    (n := pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) hm ht ha rfl
    (hroot := hm.rootClean)
  · simpa only [currentFrame_pushMethodFrame, requiredClosureFrame, Option.getD_none, popMethodFrame] using scope.self
  · simpa only [currentFrame_pushMethodFrame, requiredClosureFrame, popMethodFrame] using scope.block
  · simpa only [currentFrame_pushMethodFrame, requiredClosureFrame, popMethodFrame] using scope.cref
  · simpa only [currentFrame_pushMethodFrame, requiredClosureFrame, Option.getD_none, popMethodFrame] using scope.owner
  · exact hk
  · simp [FrameInRange, pushMethodFrame]
  · exact iteratorClosureFrame_envOk hm hu hc hargs htypes hmove
  · simp [FrameOk, currentFrame_pushMethodFrame, requiredClosureFrame]
  · simp [currentFrame_pushMethodFrame, requiredClosureFrame]
  · simp only [currentFrame_pushMethodFrame, requiredClosureFrame]
    have hl : CaptureLive m cl.captured := CaptureLive.frames_preserved
      (m := popMethodFrame m) (n := m) (Nat.le_refl _) (fun _ _ => rfl)
      (by rw [hc]; exact hm.toStateCore.captureLive)
    exact hl.pushMethodFrame _

#print axioms iteratorClosureFrame_envOk
#print axioms iteratorClosureFrame_state
end Checker.Soundness.Typed
