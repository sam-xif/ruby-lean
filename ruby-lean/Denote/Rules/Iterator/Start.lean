import Denote.Rules.Iterator.TypedEach

/-! The native iterator allocates an inert activation. Its caller projection retains
the new frame in the store; ordinary caller conformance must survive that allocation. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem iterator_push_caller_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hu : RootUncaptured m) (f : RubyCore.Frame) (hc : f.captured = none)
    (hΓ : ∀ p ∈ Γ, activationStableB p.2 = true) :
    StateOk κ Γ I (popMethodFrame (pushMethodFrame m f)) := by
  have hp := method_pop_framed hm.frameInRange.2 hc (Framed.refl (pushMethodFrame m f))
  have hcur := method_pop_currentFrame hm.frameInRange hc (Framed.refl (pushMethodFrame m f))
  have hread := method_pop_getLocal hm.frameInRange.2 hu hc (Framed.refl (pushMethodFrame m f))
  have he : EnvOk Γ (popMethodFrame (pushMethodFrame m f)) := by
    constructor
    · intro x τ hx
      obtain ⟨y, hy⟩ := envGet?_mem hx
      obtain ⟨hd, halias⟩ := hm.env.1 x τ hx
      refine ⟨?_, ?_⟩
      · rw [hread]
        exact denM_stripAlias.mpr (activationStable_heap (m := m) (hΓ (y, τ) hy) rfl (denM_stripAlias.mp hd))
      · intro z σ hz
        rw [hread, hread]
        exact halias z σ hz
    · intro x hx
      rw [hread]
      exact hm.env.2 x hx
  exact StateOk_reframe hm ht ha rfl
    (congrArg RubyCore.Frame.self hcur) (congrArg RubyCore.Frame.blk hcur)
    (congrArg RubyCore.Frame.cref hcur) (congrArg RubyCore.Frame.defmod hcur)
    (congrArg RubyCore.Frame.captured hcur) rfl
    (fun hn => by simpa only [defaultDefVis, hcur] using hm.classRuntime.visibility hn)
    (fun _ => rfl)
    ⟨by rw [hp.stack]; exact hm.frameInRange.1,
      by rw [hp.stack]; exact Nat.lt_of_lt_of_le hm.frameInRange.2 hp.frames.size⟩
    he (hp.frameOk hm.frame hcur)
    (by rw [hcur]; exact hm.localAlias)
    (by rw [hcur]
        exact hm.capturedLive.capture_preserved hp.frames.size
          (hp.frames.captured hp.stack) (hp.frames.localAlias hp.stack))

def eachFrame (m : Machine) (o : ObjId) : RubyCore.Frame :=
  { self := .ref o, defmod := classOf m.heap (.ref o), kind := .method, meth := "each",
    cref := m.currentFrame.cref }

theorem startIter_each (m : Machine) (cl : Closure) (o : ObjId) (hk : m.kont = []) :
    Interp.startIter m (.ref o) "each" cl [] (.arrayEach o 0) [] (.ref o) =
      eachArrayStep (pushMethodFrame m (eachFrame m o)) cl m.frames.size o 0 := by
  simp only [Interp.startIter, eachArrayStep, pushMethodFrame, eachFrame, hk]

theorem typed_each_start {κ : Ctx} {Γ Γb : Env} {I σ ρ : Ty} {m : Machine}
    {cl : Closure} {name : String} {names : List String} {body : Ratchet.Expr} {o : ObjId}
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots names (withoutNames ([name] ++ cl.locals) Γb) m)
    (hv : denM (.arrayOf σ) m (.ref o))
    (hmain : closureMainB κ I = true) (hσ : FirstOrder σ = true)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby body)
    (hin : activationEnvB ([(name, σ)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, σ)] ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I) :
    StepSpec m Γ (.arrayOf σ)
      (Interp.startIter m (.ref o) "each" cl [] (.arrayEach o 0) [] (.ref o)) κ I := by
  have hmain' := hmain
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain'
  obtain ⟨hr, _, _, hasm, hself, hblock, hconst, hi⟩ := hmain'
  have hu : RootUncaptured m := by
    rw [RootUncaptured, ← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime hr).captured
  let f := eachFrame m o
  have hf : f.captured = none := rfl
  have hfr := method_pop_framed hm.frameInRange.2 hf (Framed.refl (pushMethodFrame m f))
  have hs := iterator_push_caller_state hm (ReframeFO.empty hi hself hblock hconst) hasm hu f hf
    (by
      intro p hp
      have h := List.all_eq_true.mp hin p (List.mem_append_right _ hp)
      simp only [Bool.and_eq_true] at h
      exact h.1)
  have hd' : CaptureSlots names (withoutNames ([name] ++ cl.locals) Γb)
      (popMethodFrame (pushMethodFrame m f)) := by
    intro x τ hx
    rw [show (popMethodFrame (pushMethodFrame m f)).stack = m.stack from hfr.stack]
    exact (closure_saved_bindings (Framed.refl (pushMethodFrame m f)).frames
      _ hm.frameInRange.2 x).trans (hd x τ hx)
  have h := typed_each_step hs hc hd'
    ((denM_heap_only (τ := .arrayOf σ) (m₁ := m)
      (m₂ := popMethodFrame (pushMethodFrame m f)) hσ rfl).mp hv)
    hmain hσ hp he hin hout hfix hb m.frames.size 0
  rw [startIter_each m cl o hk]
  exact h.rebase hfr

#print axioms iterator_push_caller_state
#print axioms typed_each_start
end Ratchet.Denote.Typed
