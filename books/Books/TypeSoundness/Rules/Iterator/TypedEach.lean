import Books.TypeSoundness.Rules.Iterator.Each
import Books.TypeSoundness.Rules.Iterator.Caller

/-! A checked body establishes the live each loop contract. Sorbet's stable captured
types become a checked return-environment fixed point (clink 224's measurements).
Receiver payloads may grow or change; first-order element typing survives every body. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

/-- The iterator is already active; its caller supplies ordinary conformance, capture
ownership and receiver typing. Entry/source dispatch will establish these initial facts. -/
theorem typed_each_step {κ : Ctx} {Γ Γb : Env} {I σ ρ : Ty} {m : Machine}
    {cl : Closure} {name : String} {names : List String} {body : Checker.Expr} {o : ObjId}
    (hm : StateOk κ Γ I (popMethodFrame m))
    (hc : cl.captured = some ((popMethodFrame m).stack.headD 0))
    (hd : CaptureSlots names (withoutNames ([name] ++ cl.locals) Γb) (popMethodFrame m))
    (hv : denM (.arrayOf σ) (popMethodFrame m) (.ref o))
    (hmain : closureMainB κ I = true) (hσ : FirstOrder σ = true)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby body)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none)
    (hin : activationEnvB ([(name, σ)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, σ)] ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I)
    (brk : FrameId) (index : Nat) :
    StepSpec (popMethodFrame m) Γ (.arrayOf σ) (eachArrayStep m cl brk o index) κ I := by
  have hmain' := hmain
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain
  obtain ⟨hr, _, _, _, _, _, _, _⟩ := hmain
  let P := fun n (_ : Nat) => IteratorCaller (popMethodFrame m) κ Γ I σ o cl name names Γb n
  have contract : EachArrayContract (popMethodFrame m) cl name body o P Γ (.arrayOf σ) κ I
      Γb ρ (closureBodyCtx κ) I := by
    refine ⟨hp, he, henum, hfor, fun n _ hn => hn.state.rootClean, ?_, ?_, ?_, ?_, ?_⟩
    · intro n _ hn
      obtain ⟨o', xs, ho, hx, _⟩ := array_payload hn.receiver
      cases ho
      exact ⟨xs, hx⟩
    · intro n i hn xs hx hidx
      exact hb _ (hn.bodyState hmain' hin (iterator_element hn.receiver hx i hidx))
    · intro n i hn xs hx hidx v out hres
      exact (hn.next hmain' hσ hin hout hfix hres).2
    · intro n _ hn
      exact ⟨hn.framed, hn.receiver, fun _ _ => hn.state⟩
    · intro n i hn xs hx hidx j out hres
      have hu : RootUncaptured (popMethodFrame n) := by
        rw [RootUncaptured, ← currentFrame_headD hn.state.frameInRange.1]
        exact (hn.state.runtime hr).captured
      have hret := iterator_escape_result (Γ := Γ) (τ := .arrayOf σ) (κ := κ) (I := I)
        hn.state.frameInRange hu hn.capture hn.state.headAlias rfl hres
      exact ⟨hn.framed.trans hret.1, hret.2⟩
  exact eachArrayStep_spec contract brk m index ⟨hm, .refl _, hc, hd, hv⟩

#print axioms typed_each_step
end Checker.Soundness.Typed
