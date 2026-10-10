import Books.TypeSoundness.Checker.Guards.CallWorld
import Books.TypeSoundness.Rules.Instance.MainReturn
import Books.TypeSoundness.Rules.Instance.InstanceCallerReturn
import Books.TypeSoundness.Rules.Singleton.SingletonReturn

/-! One caller interface, derived from main, instance or singleton conformance. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem call_world_phase_scope {κ κb : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hw : CallWorld (returnScopeCtx κ κb)) : m.preludeMode = false := by
  cases hw with
  | main hr _ _ => exact (hm.runtime hr).phase
  | inst _ ho _ _ _ => obtain ⟨_, hs⟩ := hm.classRuntime _ ho; exact hs.phase
  | singleton _ _ ho _ _ => obtain ⟨_, _, hs⟩ := hm.singletonRuntime _ ho; exact hs.phase

theorem call_world_phase {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hw : CallWorld κ) : m.preludeMode = false :=
  call_world_phase_scope (κb := κ) hm hw

theorem call_world_uncaptured_scope {κ κb : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hw : CallWorld (returnScopeCtx κ κb)) : RootUncaptured m := by
  unfold RootUncaptured
  rw [rootFrame_eq_currentFrame hm.frameInRange.1]
  cases hw with
  | main hr _ _ => exact (hm.runtime hr).captured
  | inst _ ho _ _ _ => obtain ⟨_, hs⟩ := hm.classRuntime _ ho; exact hs.captured
  | singleton _ _ ho _ _ => obtain ⟨_, _, hs⟩ := hm.singletonRuntime _ ho; exact hs.captured

theorem call_world_uncaptured {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hw : CallWorld κ) : RootUncaptured m :=
  call_world_uncaptured_scope (κb := κ) hm hw

/-- Outgoing tables retain the classes needed by the saved caller's scope. -/
theorem call_world_restore_state {κ κb : Ctx} {Γ Γb : Env} {I Ib : Ty} {m n : Machine}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hw : CallWorld (returnScopeCtx κ κb))
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hp : Framed m (popMethodFrame n)) (hpop : (popMethodFrame n).currentFrame = m.currentFrame)
    (he : EnvOk Γ (popMethodFrame n)) (hphase : n.preludeMode = false)
    (hn : StateOk κb Γb Ib n) : StateOk (returnScopeCtx κ κb) Γ I (popMethodFrame n) := by
  cases hw with
  | main hr hw hcl => exact restore_main_state hm ht ha hr hw hcl hk hp hpop he hphase hn
  | inst hr hcl hs ho hv => exact restore_instance_state hm ht ha hr hcl hs ho hv hk hp hpop he hphase hn
  | singleton hr hcl hsg hs ho => exact restore_singleton_state hm ht ha hr hcl hsg hs ho hk hp hpop he hphase hn

theorem call_world_pop_state {κ : Ctx} {Γ Γb : Env} {I Ib : Ty} {m n : Machine}
    {f : RubyCore.Frame} {fr : Checker.Frame}
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
  | singleton hr hcl hsg hs ho =>
    exact instance_pop_singleton_state hm ht ha hr hcl hsg hs ho hu hc hk hΓ h hn

#print axioms call_world_pop_state

/-- A singleton callee returns to any retained caller world, including another singleton. -/
theorem singleton_call_pop_state {κ : Ctx} {Γ Γb : Env} {I : Ty} {m n : Machine}
    {f : RubyCore.Frame} {cn name : String}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hw : CallWorld κ) (hc : f.captured = none)
    (hk : ∀ x, constGet? (singletonBodyCtx κ cn name) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (h : Framed (pushMethodFrame m f) n)
    (hn : StateOk (singletonBodyCtx κ cn name) Γb .ivar0 n) : StateOk κ Γ I (popMethodFrame n) := by
  have hu := call_world_uncaptured hm hw
  have hp := method_pop_framed hm.frameInRange.2 hc h
  have hpop := method_pop_currentFrame hm.frameInRange hc h
  have he := method_pop_envOk hm.frameInRange.2 hu hc h hm.env hΓ hm.localAlias_getD
  obtain ⟨_, _, scope⟩ := hn.singletonRuntime cn rfl
  cases hw with
  | main hr hw hcl =>
    exact restore_main_state (κb := singletonBodyCtx κ cn name) hm ht ha hr hw hcl hk hp hpop he scope.phase hn
  | inst hr hcl hs ho hv =>
    exact restore_instance_state (κb := singletonBodyCtx κ cn name) hm ht ha hr hcl hs ho hv hk hp hpop he scope.phase hn
  | singleton hr hcl hsg hs ho =>
    exact restore_singleton_state (κb := singletonBodyCtx κ cn name) hm ht ha hr hcl hsg hs ho hk hp hpop he scope.phase hn

#print axioms singleton_call_pop_state
end Checker.Soundness.Typed
