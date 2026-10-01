import Denote.Rules.Closure.State
import Denote.Sem.Closure.Reify

/-! Full captured entry from a conformant ordinary caller. These controls instantiate
the capture's complete environment and real lexical scope, not only its value spine. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ClosureStateControls
open RubyCore Ratchet Ratchet.Denote

theorem current_capture_entry {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hu : m.currentFrame.captured = none) (ps : List SigParam) (args : List Value)
    (ls : List String) (body : RubyCore.Expr) (hargs : DenAll (ps.map (·.2)) m args)
    (hlen : args.length = ps.length)
    (htypes : ∀ p ∈ ps ++ blockLocals ls ++ Γ,
      FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (κ.withFrame none) x = constGet? κ x) :
    ∃ n, Interp.callClosure m
        (reifiedClosure m ((ps.map (·.1)).map RubyCore.Param.req) ls body true) args none = .next n ∧
      StateOk (κ.withoutRuntimeScope.withFrame none) (ps ++ blockLocals ls ++ Γ) I n := by
  apply callClosure_required_state hm ht ha (ClosureScopeEq.current hm.frameInRange rfl)
    (ps := ps) (cap := Γ)
  · apply CaptureLive.frame hm.frameInRange.2
    rw [← currentFrame_headD hm.frameInRange.1, hu]
    exact .none
  · exact hargs
  · intro x τ hx
    obtain ⟨z, hz⟩ := envGet?_mem hx
    have ht := (htypes (z, τ) (List.mem_append_right _ hz)).2
    have hs : stripAlias τ = τ := by cases τ <;> simp_all [stripAlias, isAliasTy]
    rw [closLocal_current rfl]
    simpa only [hs] using (hm.env.1 x τ hx).1
  · intro x hx
    rw [closLocal_current rfl]
    exact hm.env.2 x hx
  · exact htypes
  · exact hk
  · rfl
  · rfl
  · exact hlen

theorem boot_entry (hb : bootOkB = true) (value : Int) :
    ∃ n, Interp.callClosure bootMachine
        (reifiedClosure bootMachine [] [] (.int value) true) [] none = .next n ∧
      StateOk (ctx0.withoutRuntimeScope.withFrame none) [] .ivar0 n :=
  current_capture_entry (stateOk_boot hb) (ReframeFO.empty rfl rfl rfl rfl) rfl
    ((stateOk_boot hb).runtime rfl).captured [] [] [] (.int value) trivial rfl
    (by simp [blockLocals]) (fun _ => rfl)

/-- An ordinary MainReady promise would contradict the actual captured activation. -/
theorem captured_not_main {m : Machine} {cl : Closure} {fid : FrameId}
    (hc : cl.captured = some fid) (names : List String) (args : List Value) :
    ¬ MainReady (pushMethodFrame m (requiredClosureFrame m cl names args)) := by
  intro h
  have hp := h.captured
  simp only [currentFrame_pushMethodFrame, requiredClosureFrame, hc] at hp
  cases hp

/-- An empty lower-bound capture spine cannot establish an empty body environment. -/
theorem empty_spine_not_env {m : Machine} {cl : Closure}
    (hl : CaptureLive m cl.captured) (hls : cl.locals = [])
    (hx : closLocal m cl "x" = .int 7) :
    denSpine .ivar0 m (closLocal m cl) ∧
    ¬ EnvOk [] (pushMethodFrame m (requiredClosureFrame m cl [] [])) := by
  refine ⟨by simp [denSpine, denSpineFrom], ?_⟩
  intro he
  have hn := he.2 "x" rfl
  rw [requiredClosureFrame_getLocal m cl [] [] none none hl, hls] at hn
  simp only [List.map_nil, List.zip_nil_left, List.nil_append, List.find?_nil, hx] at hn
  cases hn

#print axioms current_capture_entry
#print axioms boot_entry
#print axioms captured_not_main
#print axioms empty_spine_not_env
end Ratchet.Denote.Typed.ClosureStateControls
