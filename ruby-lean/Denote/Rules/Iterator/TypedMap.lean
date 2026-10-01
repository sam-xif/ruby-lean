import Denote.Rules.Iterator.Map
import Denote.Rules.Iterator.Caller
import Denote.Rules.Expr.Array

/-! A checked map body preserves the caller and a typed result accumulator. Sorbet
0.6.13405 uses the body result type as the output element type, while requiring captured
types to remain stable (clink 228). First-order results survive later body effects. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- The iterator is already active; its caller supplies ordinary conformance, capture
ownership and receiver typing. Entry/source dispatch will establish these initial facts. -/
theorem typed_map_step {κ : Ctx} {Γ Γb : Env} {I σ ρ : Ty} {m : Machine}
    {cl : Closure} {name : String} {names : List String} {body : Ratchet.Expr} {o : ObjId}
    (hm : StateOk κ Γ I (popMethodFrame m))
    (hc : cl.captured = some ((popMethodFrame m).stack.headD 0))
    (hd : CaptureSlots names (withoutNames ([name] ++ cl.locals) Γb) (popMethodFrame m))
    (hv : denM (.arrayOf σ) (popMethodFrame m) (.ref o))
    (hmain : closureMainB κ I = true) (hσ : FirstOrder σ = true) (hρ : FirstOrder ρ = true)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby body)
    (hin : activationEnvB ([(name, σ)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, σ)] ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I)
    (brk : FrameId) (index : Nat) (acc : List Value)
    (ha : ∀ v ∈ acc, denM ρ (popMethodFrame m) v) :
    StepSpec (popMethodFrame m) Γ (.arrayOf ρ) (mapArrayStep m cl brk o index acc) κ I := by
  have hmain' := hmain
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain
  obtain ⟨hr, _, _, _, _, _, _, _⟩ := hmain
  let P := fun n (_ : Nat) (acc : List Value) =>
    IteratorCaller (popMethodFrame m) κ Γ I σ o cl name names Γb n ∧
      ∀ v ∈ acc, denM ρ (popMethodFrame n) v
  have contract : MapArrayContract (popMethodFrame m) cl name body o P Γ (.arrayOf ρ) κ I
      Γb ρ (closureBodyCtx κ) I := by
    refine ⟨hp, he, ?_, ?_, ?_, ?_, ?_⟩
    · intro n _ acc hn
      obtain ⟨o', xs, ho, hx, _⟩ := array_payload hn.1.receiver
      cases ho
      exact ⟨xs, hx⟩
    · intro n i acc hn xs hx hidx
      exact hb _ (hn.1.bodyState hmain' hin (iterator_element hn.1.receiver hx i hidx))
    · intro n i acc hn xs hx hidx v out hres
      obtain ⟨hf, hn'⟩ := hn.1.next hmain' hσ hin hout hfix hres
      refine ⟨hn', ?_⟩
      intro w hw
      apply (denM_heap_only (m₁ := popMethodFrame (popMethodFrame out))
        (m₂ := popMethodFrame (deliverA (.val v) (popMethodFrame out) [])) hρ rfl).mp
      rcases List.mem_append.mp hw with hw | hw
      · exact hf.firstOrder ρ hρ w (hn.2 w hw)
      · have hw : w = v := List.mem_singleton.mp hw
        subst w
        exact (denM_heap_only (m₁ := out) (m₂ := popMethodFrame (popMethodFrame out)) hρ rfl).mp hres.2.1
    · intro n _ acc hn
      have h := array_alloc_result hn.1.state acc hn.2
      exact ⟨hn.1.framed.trans h.1, h.2⟩
    · intro n i acc hn xs hx hidx j out hres
      have hu : RootUncaptured (popMethodFrame n) := by
        rw [RootUncaptured, ← currentFrame_headD hn.1.state.frameInRange.1]
        exact (hn.1.state.runtime hr).captured
      have hret := iterator_escape_result (Γ := Γ) (τ := .arrayOf ρ) (κ := κ) (I := I)
        hn.1.state.frameInRange hu hn.1.capture hres
      exact ⟨hn.1.framed.trans hret.1, hret.2⟩
  exact mapArrayStep_spec contract brk m index acc ⟨⟨hm, .refl _, hc, hd, hv⟩, ha⟩

#print axioms typed_map_step
end Ratchet.Denote.Typed
