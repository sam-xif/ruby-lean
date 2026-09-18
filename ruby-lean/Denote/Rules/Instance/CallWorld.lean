import Ratchet.Guards.CallWorld
import Denote.Rules.Instance.MainReturn
import Denote.Rules.Instance.InstanceCallerReturn

/-! One caller interface, derived from main or instance conformance. No new state field. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem call_world_phase {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hw : CallWorld κ) : m.preludeMode = false := by
  cases hw with
  | main hr _ _ => exact (hm.runtime hr).phase
  | inst _ ho _ _ _ => obtain ⟨_, hs⟩ := hm.classRuntime _ ho; exact hs.phase

theorem call_world_uncaptured {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hw : CallWorld κ) : RootUncaptured m := by
  unfold RootUncaptured
  rw [rootFrame_eq_currentFrame hm.frameInRange.1]
  cases hw with
  | main hr _ _ => exact (hm.runtime hr).captured
  | inst _ ho _ _ _ => obtain ⟨_, hs⟩ := hm.classRuntime _ ho; exact hs.captured

theorem call_world_pop_state {κ : Ctx} {Γ Γb : Env} {I Ib : Ty} {m n : Machine}
    {f : RubyCore.Frame} {fr : Ratchet.Frame}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hw : CallWorld κ) (hc : f.captured = none)
    (hk : ∀ x, constGet? (instanceBodyCtx κ fr Ib) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (h : Framed (pushMethodFrame m f) n)
    (hn : StateOk (instanceBodyCtx κ fr Ib) Γb Ib n) : StateOk κ Γ I (popMethodFrame n) := by
  have hu := call_world_uncaptured hm hw
  cases hw with
  | main hr hw hcl => exact instance_pop_main_state hm ht ha hr hw hcl hu hc hk hΓ h hn
  | inst hr hcl hs ho hv => exact instance_pop_instance_state hm ht ha hr hcl hs ho hv hu hc hk hΓ h hn

#print axioms call_world_pop_state
end Ratchet.Denote.Typed
