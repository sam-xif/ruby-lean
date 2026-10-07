import Books.TypeSoundness.Rules.Iterator.Entry
import Books.TypeSoundness.Rules.Iterator.ReturnState
import Books.TypeSoundness.Rules.Closure.FlowCall
import Books.TypeSoundness.Rules.Expr.ArrayIndex

/-! Shared caller invariant for native Array iterators. The active iterator is inert;
entry and return conformance belong to its captured caller, two frame pops below the body. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

structure IteratorCaller (origin : Machine) (κ : Ctx) (Γ : Env) (I σ : Ty)
    (o : ObjId) (cl : Closure) (name : String) (names : List String) (Γb : Env) (m : Machine) : Prop where
  state : StateOk κ Γ I (popMethodFrame m)
  framed : Framed origin (popMethodFrame m)
  capture : cl.captured = some ((popMethodFrame m).stack.headD 0)
  slots : CaptureSlots names (withoutNames ([name] ++ cl.locals) Γb) (popMethodFrame m)
  receiver : denM (.arrayOf σ) (popMethodFrame m) (.ref o)

theorem iterator_element {m : Machine} {o : ObjId} {σ : Ty} {xs : Array Value}
    (hd : denM (.arrayOf σ) (popMethodFrame m) (.ref o))
    (hx : (m.heap.get o).payload = .arr xs) (i : Nat) (hi : i < xs.size) :
    DenAll [σ] (popMethodFrame m) [xs[i]] := by
  obtain ⟨o', ys, ho, hy, hd⟩ := array_payload hd
  cases ho
  have he : ys = xs := by simpa only [popMethodFrame, hx, Payload.arr.injEq] using hy.symm
  subst ys
  exact ⟨hd _ (Array.getElem_mem hi), trivial⟩

theorem IteratorCaller.bodyState {origin m : Machine} {κ : Ctx} {Γ Γb : Env} {I σ : Ty}
    {o : ObjId} {cl : Closure} {name : String} {names : List String} {arg : Value}
    (hn : IteratorCaller origin κ Γ I σ o cl name names Γb m)
    (hmain : closureMainB κ I = true)
    (hin : activationEnvB ([(name, σ)] ++ blockLocals cl.locals ++ Γ) = true)
    (hv : DenAll [σ] (popMethodFrame m) [arg]) :
    StateOk (closureBodyCtx κ) ([(name, σ)] ++ blockLocals cl.locals ++ Γ) I
      (pushMethodFrame m (requiredClosureFrame m cl [name] [arg])) := by
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain
  obtain ⟨hr, _, _, hasm, hself, hblock, hconst, hi⟩ := hmain
  have hi' p (hp : p ∈ [(name, σ)] ++ blockLocals cl.locals ++ Γ) := List.all_eq_true.mp hin p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi'
  exact iteratorClosureFrame_state hn.state (ReframeFO.empty hi hself hblock hconst) hasm
    (hn.state.runtime hr).captured hn.capture hv
    (fun p hp => (hi' p hp).2)
    (fun p hp _ hv => activationStable_heap (m := popMethodFrame m) (hi' p hp).1 rfl hv)
    (fun x => (constGet?_empty (κ := κ.withFrame none) hconst x).trans
      (constGet?_empty hconst x).symm)

/-- Preserve caller state and physical capture ownership after a checked body. The
relative framing fact also transports map's already collected values. -/
theorem IteratorCaller.next {origin m out : Machine} {κ : Ctx} {Γ Γb : Env} {I σ ρ : Ty}
    {o : ObjId} {cl : Closure} {name : String} {names : List String} {arg v : Value}
    (hn : IteratorCaller origin κ Γ I σ o cl name names Γb m)
    (hmain : closureMainB κ I = true) (hσ : FirstOrder σ = true)
    (hin : activationEnvB ([(name, σ)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hres : ResultOk (pushMethodFrame m (requiredClosureFrame m cl [name] [arg]))
      Γb ρ (.val v) out (closureBodyCtx κ) I) :
    Framed (popMethodFrame m) (popMethodFrame (popMethodFrame out)) ∧
    IteratorCaller origin κ Γ I σ o cl name names Γb
      (deliverA (.val v) (popMethodFrame out) []) := by
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain
  obtain ⟨hr, hw, hclass, hasm, hself, hblock, hconst, hi⟩ := hmain
  have hi' p (hp : p ∈ [(name, σ)] ++ blockLocals cl.locals ++ Γ) := List.all_eq_true.mp hin p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi'
  have hctx : returnScopeCtx κ (closureBodyCtx κ) = κ := by cases κ; rfl
  have hu : RootUncaptured (popMethodFrame m) := by
    rw [RootUncaptured, ← currentFrame_headD hn.state.frameInRange.1]
    exact (hn.state.runtime hr).captured
  have hcap : (requiredClosureFrame m cl [name] [arg]).captured =
      some ((popMethodFrame m).stack.headD 0) := hn.capture
  have hf := iterator_pop_framed hn.state.frameInRange.2 hu hcap hres.1 hn.state.headAlias rfl
  have hs := iterator_return_main_state (κb := closureBodyCtx κ) hn.state
    (ReframeFO.empty hi hself hblock hconst) hasm hr hw hclass
    (fun x => (constGet?_empty (κ := closureBodyCtx κ) hconst x).trans
      (constGet?_empty (κ := returnScopeCtx κ (closureBodyCtx κ)) hconst x).symm)
    hcap rfl hn.slots (requiredClosureFrame_slots m cl [name] [arg] rfl)
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
  refine ⟨hf, ?_⟩
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

#print axioms IteratorCaller.bodyState
#print axioms IteratorCaller.next
end Checker.Soundness.Typed
