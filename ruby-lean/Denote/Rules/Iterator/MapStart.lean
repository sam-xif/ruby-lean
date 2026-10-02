import Denote.Rules.Iterator.Start
import Denote.Rules.Iterator.TypedMap

/-! Enter the native map/collect activation, preserving the projected caller and
starting the checked loop with an empty result accumulator. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def mapFrame (m : Machine) (o : ObjId) (mname : String) : RubyCore.Frame :=
  { self := .ref o, defmod := classOf m.heap (.ref o), kind := .method, meth := mname,
    cref := m.currentFrame.cref, matchXparent := mname == "scan" }

theorem startIter_map (m : Machine) (cl : Closure) (o : ObjId) (mname : String) (hk : m.kont = []) :
    Interp.startIter m (.ref o) mname cl [] (.arrayMap o 0) [] .nil =
      mapArrayStep (pushMethodFrame m (mapFrame m o mname)) cl m.frames.size o 0 [] := by
  simp only [Interp.startIter, mapArrayStep, pushMethodFrame, mapFrame, hk]

theorem typed_map_start {κ : Ctx} {Γ Γb : Env} {I σ ρ : Ty} {m : Machine}
    {cl : Closure} {name : String} {names : List String} {body : Ratchet.Expr} {o : ObjId} {mname : String}
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots names (withoutNames ([name] ++ cl.locals) Γb) m)
    (hv : denM (.arrayOf σ) m (.ref o))
    (hmain : closureMainB κ I = true) (hσ : FirstOrder σ = true) (hρ : FirstOrder ρ = true)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby body)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none)
    (hin : activationEnvB ([(name, σ)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, σ)] ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I) :
    StepSpec m Γ (.arrayOf ρ)
      (Interp.startIter m (.ref o) mname cl [] (.arrayMap o 0) [] .nil) κ I := by
  have hmain' := hmain
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain'
  obtain ⟨hr, _, _, hasm, hself, hblock, hconst, hi⟩ := hmain'
  have hu : RootUncaptured m := by
    rw [RootUncaptured, ← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime hr).captured
  let f := mapFrame m o mname
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
  have h := typed_map_step hs hc hd'
    ((denM_heap_only (τ := .arrayOf σ) (m₁ := m)
      (m₂ := popMethodFrame (pushMethodFrame m f)) hσ rfl).mp hv)
    hmain hσ hρ hp he henum hfor hin hout hfix hb m.frames.size 0 [] (by simp)
  rw [startIter_map m cl o mname hk]
  exact h.rebase hfr

#print axioms typed_map_start
end Ratchet.Denote.Typed
