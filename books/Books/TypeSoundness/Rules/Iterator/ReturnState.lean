import Books.TypeSoundness.Rules.Iterator.ReturnEnv
import Books.TypeSoundness.Rules.Instance.MainReturn

/-! Restore the main caller's full state after the block and inert iterator pops.
The body supplies the updated heap world; the merged environment accounts for capture
writes and parameter/block-local shadowing. Escapes retain framing without a value state. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem iterator_return_main_state {κ κb : Ctx} {Γ Γb : Env} {I Ib : Ty}
    {m n : Machine} {f : RubyCore.Frame} {shadow names : List String}
    (hm : StateOk κ Γ I (popMethodFrame m)) (ht : ReframeFO (returnScopeCtx κ κb) I)
    (ha : κ.asms = []) (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hc : f.captured = some ((popMethodFrame m).stack.headD 0)) (hfa : f.localAlias = none)
    (hd : CaptureSlots names (withoutNames shadow Γb) (popMethodFrame m))
    (hf : ∀ x, f.locals.any (·.1 == x) = shadow.contains x)
    (h : Framed (pushMethodFrame m f) n) (hn : StateOk κb Γb Ib n)
    (hbefore : ∀ x τ, envGet? Γ x = some τ → ∀ v, denM (stripAlias τ) (popMethodFrame m) v →
      denM (stripAlias τ) (popMethodFrame (popMethodFrame n)) v)
    (hafter : ∀ x τ, envGet? Γb x = some τ → names.contains x = true → ∀ v,
      denM (stripAlias τ) n v → denM (stripAlias τ) (popMethodFrame (popMethodFrame n)) v) :
    StateOk (returnScopeCtx κ κb) (closureReturnEnv shadow names Γ Γb) I
      (popMethodFrame (popMethodFrame n)) := by
  have hu : RootUncaptured (popMethodFrame m) := by
    rw [RootUncaptured, ← currentFrame_headD hm.frameInRange.1]
    exact (hm.runtime hr).captured
  exact restore_main_state_atStack (n := n) (s := n.stack.tail.tail) hm ht ha hr hw hcl hk
    (iterator_pop_framed hm.frameInRange.2 hu hc h hm.headAlias hfa)
    (iterator_pop_metadata hm.frameInRange h)
    (iterator_return_env hm.frameInRange hu hc hd hf h hm.env hn.env hm.headAlias hfa hbefore hafter)
    (h.phase.trans (hm.runtime hr).phase) hn

theorem iterator_escape_result {m n : Machine} {f : RubyCore.Frame}
    {Γ Γb : Env} {τ ρ I Ib : Ty} {κ κb : Ctx} {j : Jump}
    (hl : FrameInRange (popMethodFrame m)) (hu : RootUncaptured (popMethodFrame m))
    (hc : f.captured = some ((popMethodFrame m).stack.headD 0))
    (hal : (m.frames.getD ((popMethodFrame m).stack.headD 0) default).localAlias = none)
    (hfa : f.localAlias = none)
    (h : ResultOk (pushMethodFrame m f) Γb ρ (.esc j) n κb Ib) :
    ResultOk (popMethodFrame m) Γ τ (.esc j) (popMethodFrame (popMethodFrame n)) κ I := by
  refine ⟨iterator_pop_framed hl.2 hu hc h.1 hal hfa, ?_, fun _ hv => by cases hv⟩
  cases j <;> exact h.2.1

#print axioms iterator_return_main_state
#print axioms iterator_escape_result
end Checker.Soundness.Typed
