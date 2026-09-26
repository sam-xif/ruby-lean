import Denote.Rules.Iterator.Each
import Denote.Rules.Iterator.Entry
import Denote.Rules.Iterator.ReturnState
import Denote.Rules.Closure.FlowCall
import Denote.Rules.Expr.ArrayIndex

/-! A checked body establishes the live each loop contract. Sorbet's stable captured
types become a checked return-environment fixed point (clink 224's measurements).
Receiver payloads may grow or change; first-order element typing survives every body. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private structure EachCaller (origin : Machine) (κ : Ctx) (Γ : Env) (I σ : Ty)
    (o : ObjId) (cl : Closure) (name : String) (names : List String) (Γb : Env) (m : Machine) : Prop where
  state : StateOk κ Γ I (popMethodFrame m)
  framed : Framed origin (popMethodFrame m)
  capture : cl.captured = some ((popMethodFrame m).stack.headD 0)
  slots : CaptureSlots names (withoutNames ([name] ++ cl.locals) Γb) (popMethodFrame m)
  receiver : denM (.arrayOf σ) (popMethodFrame m) (.ref o)

private theorem each_element {m : Machine} {o : ObjId} {σ : Ty} {xs : Array Value}
    (hd : denM (.arrayOf σ) (popMethodFrame m) (.ref o))
    (hx : (m.heap.get o).payload = .arr xs) (i : Nat) (hi : i < xs.size) :
    DenAll [σ] (popMethodFrame m) [xs[i]] := by
  obtain ⟨o', ys, ho, hy, hd⟩ := array_payload hd
  cases ho
  have he : ys = xs := by simpa only [popMethodFrame, hx, Payload.arr.injEq] using hy.symm
  subst ys
  exact ⟨hd _ (Array.getElem_mem hi), trivial⟩

/-- The iterator is already active; its caller supplies ordinary conformance, capture
ownership and receiver typing. Entry/source dispatch will establish these initial facts. -/
theorem typed_each_step {κ : Ctx} {Γ Γb : Env} {I σ ρ : Ty} {m : Machine}
    {cl : Closure} {name : String} {names : List String} {body : Ratchet.Expr} {o : ObjId}
    (hm : StateOk κ Γ I (popMethodFrame m))
    (hc : cl.captured = some ((popMethodFrame m).stack.headD 0))
    (hd : CaptureSlots names (withoutNames ([name] ++ cl.locals) Γb) (popMethodFrame m))
    (hv : denM (.arrayOf σ) (popMethodFrame m) (.ref o))
    (hmain : closureMainB κ I = true) (hσ : FirstOrder σ = true)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby body)
    (hin : activationEnvB ([(name, σ)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, σ)] ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I)
    (brk : FrameId) (index : Nat) :
    StepSpec (popMethodFrame m) Γ (.arrayOf σ) (eachArrayStep m cl brk o index) κ I := by
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain
  obtain ⟨hr, hw, hclass, hasm, hself, hblock, hconst, hi⟩ := hmain
  have hi' p (hp : p ∈ [(name, σ)] ++ blockLocals cl.locals ++ Γ) := List.all_eq_true.mp hin p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi'
  have hctx : returnScopeCtx κ (closureBodyCtx κ) = κ := by cases κ; rfl
  let P := fun n (_ : Nat) => EachCaller (popMethodFrame m) κ Γ I σ o cl name names Γb n
  have contract : EachArrayContract (popMethodFrame m) cl name body o P Γ (.arrayOf σ) κ I
      Γb ρ (closureBodyCtx κ) I := by
    refine ⟨hp, he, ?_, ?_, ?_, ?_, ?_⟩
    · intro n _ hn
      obtain ⟨o', xs, ho, hx, _⟩ := array_payload hn.receiver
      cases ho
      exact ⟨xs, hx⟩
    · intro n i hn xs hx hidx
      apply hb
      exact iteratorClosureFrame_state hn.state (ReframeFO.empty hi hself hblock hconst) hasm
        (hn.state.runtime hr).captured hn.capture (each_element hn.receiver hx i hidx)
        (fun p hp => (hi' p hp).2)
        (fun p hp _ hv => activationStable_heap (m := popMethodFrame n) (hi' p hp).1 rfl hv)
        (fun x => (constGet?_empty (κ := κ.withFrame none) hconst x).trans
          (constGet?_empty hconst x).symm)
    · intro n i hn xs hx hidx v out hres
      have hu : RootUncaptured (popMethodFrame n) := by
        rw [RootUncaptured, ← currentFrame_headD hn.state.frameInRange.1]
        exact (hn.state.runtime hr).captured
      have hcap : (requiredClosureFrame n cl [name] [xs[i]]).captured =
          some ((popMethodFrame n).stack.headD 0) := hn.capture
      have hf := iterator_pop_framed hn.state.frameInRange.2 hu hcap hres.1
      have hs := iterator_return_main_state (κb := closureBodyCtx κ) hn.state
        (ReframeFO.empty hi hself hblock hconst) hasm hr hw hclass
        (fun x => (constGet?_empty (κ := closureBodyCtx κ) hconst x).trans
          (constGet?_empty (κ := returnScopeCtx κ (closureBodyCtx κ)) hconst x).symm)
        hcap hn.slots (requiredClosureFrame_slots n cl [name] [xs[i]] rfl)
        hres.1 (hres.2.2 v rfl)
        (by
          intro x τ hx v hv
          obtain ⟨y, hy⟩ := envGet?_mem hx
          exact denM_stripAlias.mpr (activationStable_framed
            (hi' (y, τ) (List.mem_append_right _ hy)).1 hf (denM_stripAlias.mp hv)))
        (by
          intro x τ hx _ v hv
          obtain ⟨y, hy⟩ := envGet?_mem hx
          exact activationStable_heap (m := out) (List.all_eq_true.mp hout (y, τ) hy) rfl hv)
      rw [hfix, hctx] at hs
      refine ⟨?_, hn.framed.trans (hf.trans (Framed_reCtl _ _ _)), ?_, ?_, ?_⟩
      · simpa only [popMethodFrame, deliverA] using (StateOk_deliverA (a := .val v) (K := []) hs)
      · change cl.captured = some ((popMethodFrame (popMethodFrame out)).stack.headD 0)
        rw [hf.stack]
        exact hn.capture
      · intro x τ hx
        change frameBinds (popMethodFrame (popMethodFrame out))
          ((popMethodFrame (popMethodFrame out)).stack.headD 0) x = names.contains x
        rw [hf.stack]
        exact (closure_saved_bindings hres.1.frames _ hn.state.frameInRange.2 x).trans (hn.slots x τ hx)
      · simpa only [popMethodFrame, deliverA] using
          (denM_deliverA (a := .val v) (K := [])).mpr (hf.firstOrder (.arrayOf σ) hσ _ hn.receiver)
    · intro n _ hn
      exact ⟨hn.framed, hn.receiver, fun _ _ => hn.state⟩
    · intro n i hn xs hx hidx j out hres
      have hu : RootUncaptured (popMethodFrame n) := by
        rw [RootUncaptured, ← currentFrame_headD hn.state.frameInRange.1]
        exact (hn.state.runtime hr).captured
      have hret := iterator_escape_result (Γ := Γ) (τ := .arrayOf σ) (κ := κ) (I := I)
        hn.state.frameInRange hu hn.capture hres
      exact ⟨hn.framed.trans hret.1, hret.2⟩
  exact eachArrayStep_spec contract brk m index ⟨hm, .refl _, hc, hd, hv⟩

#print axioms typed_each_step
end Ratchet.Denote.Typed
