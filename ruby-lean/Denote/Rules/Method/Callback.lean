import Denote.Rules.Method.CallbackFrame
import Denote.Rules.Iterator.Entry
import Denote.Rules.Iterator.ReturnState
import Denote.Rules.Closure.FlowCall

/-! Full caller conformance around a required-positional callback across a method.
Sorbet 0.6.13405 checks yield arguments against the declared Proc parameters and rejects
captured type changes (clink 230). The outgoing environment therefore has a fixed point.
The suspended method retains its own locals; the captured caller may change values. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

structure CallbackCaller (κ : Ctx) (Γ : Env) (I : Ty) (cl : Closure)
    (ps : List SigParam) (names : List String) (Γb : Env) (m : Machine) : Prop where
  state : StateOk κ Γ I (popMethodFrame m)
  capture : cl.captured = some ((popMethodFrame m).stack.headD 0)
  slots : CaptureSlots names (withoutNames (ps.map (·.1) ++ cl.locals) Γb) (popMethodFrame m)

def CallbackResultOk (m : Machine) (Γ : Env) (τ : Ty) (κ : Ctx) (I : Ty)
    (a : Answer) (n : Machine) : Prop :=
  CallbackFramed m n ∧ AnsOk τ n a ∧
    (∀ v, a = .val v → StateOk κ Γ I (popMethodFrame n))

theorem CallbackCaller.bodyState {m : Machine} {κ : Ctx} {Γ Γb : Env} {I : Ty}
    {cl : Closure} {ps : List SigParam} {names : List String} {args : List Value}
    (hn : CallbackCaller κ Γ I cl ps names Γb m)
    (hmain : closureMainB κ I = true)
    (hin : activationEnvB (ps ++ blockLocals cl.locals ++ Γ) = true)
    (hv : DenAll (ps.map (·.2)) (popMethodFrame m) args) :
    StateOk (closureBodyCtx κ) (ps ++ blockLocals cl.locals ++ Γ) I
      (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) := by
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain
  obtain ⟨hr, _, _, hasm, hself, hblock, hconst, hi⟩ := hmain
  have hi' p (hp : p ∈ ps ++ blockLocals cl.locals ++ Γ) := List.all_eq_true.mp hin p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi'
  exact iteratorClosureFrame_state hn.state (ReframeFO.empty hi hself hblock hconst) hasm
    (hn.state.runtime hr).captured hn.capture hv
    (fun p hp => (hi' p hp).2)
    (fun p hp _ hv => activationStable_heap (m := popMethodFrame m) (hi' p hp).1 rfl hv)
    (fun x => (constGet?_empty (κ := κ.withFrame none) hconst x).trans
      (constGet?_empty hconst x).symm)

/-- No caller-restoration premise remains: the checked body and its environment
fixed point supply it, on top of the separate suspended-method preservation fact. -/
theorem CallbackCaller.returnResult {m out : Machine} {κ : Ctx} {Γ Γb : Env} {I ρ : Ty}
    {cl : Closure} {ps : List SigParam} {names : List String} {args : List Value} {a : Answer}
    (hn : CallbackCaller κ Γ I cl ps names Γb m)
    (hm : FrameInRange m) (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hmain : closureMainB κ I = true) (hρ : FirstOrder ρ = true)
    (hlen : args.length = ps.length)
    (hin : activationEnvB (ps ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv (ps.map (·.1) ++ cl.locals) names Γ Γb = Γ)
    (hres : ResultOk (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args))
      Γb ρ a out (closureBodyCtx κ) I) :
    CallbackResultOk m Γ ρ κ I a (popMethodFrame out) := by
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain
  obtain ⟨hr, hw, hclass, hasm, hself, hblock, hconst, hi⟩ := hmain
  have hi' p (hp : p ∈ ps ++ blockLocals cl.locals ++ Γ) := List.all_eq_true.mp hin p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi'
  have hu : RootUncaptured (popMethodFrame m) := by
    rw [RootUncaptured, ← currentFrame_headD hn.state.frameInRange.1]
    exact (hn.state.runtime hr).captured
  have hf := callback_pop_framed hm hn.state.frameInRange hne hu hn.capture hres.1
  refine ⟨hf, ?_, ?_⟩
  · cases a with
    | val v => exact (denM_heap_only (m₁ := out) (m₂ := popMethodFrame out) hρ rfl).mp hres.2.1
    | esc j => cases j <;> exact hres.2.1
  · intro v hv
    have hs := iterator_return_main_state (κb := closureBodyCtx κ) hn.state
      (ReframeFO.empty hi hself hblock hconst) hasm hr hw hclass
      (fun x => (constGet?_empty (κ := closureBodyCtx κ) hconst x).trans
        (constGet?_empty (κ := returnScopeCtx κ (closureBodyCtx κ)) hconst x).symm)
      hn.capture hn.slots (requiredClosureFrame_slots m cl (ps.map (·.1)) args (by simpa using hlen))
      hres.1 (hres.2.2 v hv)
      (by
        intro x τ hx v hv
        obtain ⟨y, hy⟩ := envGet?_mem hx
        exact denM_stripAlias.mpr (activationStable_framed
          (hi' (y, τ) (List.mem_append_right _ hy)).1 hf.caller (denM_stripAlias.mp hv)))
      (by
        intro x τ hx _ v hv
        obtain ⟨y, hy⟩ := envGet?_mem hx
        exact activationStable_heap (m := out) (List.all_eq_true.mp hout (y, τ) hy) rfl hv)
    have hctx : returnScopeCtx κ (closureBodyCtx κ) = κ := by cases κ; rfl
    simpa only [hfix, hctx] using hs

/-- A returned value restores the caller invariant for another yield of the same block.
Capture identity and physical ownership remain valid after the first captured write. -/
theorem CallbackCaller.next {m n : Machine} {κ : Ctx} {Γ Γb : Env} {I ρ : Ty}
    {cl : Closure} {ps : List SigParam} {names : List String} {v : Value}
    (hn : CallbackCaller κ Γ I cl ps names Γb m)
    (h : CallbackResultOk m Γ ρ κ I (.val v) n) : CallbackCaller κ Γ I cl ps names Γb n := by
  refine ⟨h.2.2 v rfl, ?_, ?_⟩
  · rw [h.1.caller.stack]; exact hn.capture
  · intro x τ hx
    exact (h.1.bindings x).trans (hn.slots x τ hx)

#print axioms CallbackCaller.bodyState
#print axioms CallbackCaller.returnResult
#print axioms CallbackCaller.next
end Ratchet.Denote.Typed
