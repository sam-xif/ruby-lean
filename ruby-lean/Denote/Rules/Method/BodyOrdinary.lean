import Denote.Rules.Method.BodyRun

/-! Ordinary certified expressions may change method locals while preserving the
suspended caller. Its current environment supplies the reads; the original caller,
before method allocation, anchors heap/framing restoration across earlier callbacks. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem ordinary_caller_frame {m n : Machine} (h : Framed m n)
    (hm : RootUncaptured m) (hc : FrameInRange (popMethodFrame m))
    (hne : (popMethodFrame m).stack.headD 0 ≠ m.stack.headD 0) :
    (popMethodFrame n).currentFrame = (popMethodFrame m).currentFrame := by
  rw [← rootFrame_eq_currentFrame (m := popMethodFrame n) (by
      simpa only [popMethodFrame, h.stack] using hc.1),
    ← rootFrame_eq_currentFrame hc.1]
  simpa only [popMethodFrame, h.stack] using h.frames.isolated hm _ hc.2 hne

/-- Full caller conformance after an ordinary expression. The current caller may
already contain captured writes; only its stable types, not its original values, persist.
The framing origin must precede allocation of the active method. -/
theorem ordinary_caller_state {origin m n : Machine} {κ : Ctx} {Γ₀ Γc Γm : Env}
    {I : Ty} {fr : Ratchet.Frame} {code : ClosureCode}
    (ho : StateOk κ Γ₀ I origin) (hc : StateOk κ Γc I (popMethodFrame m))
    (hu : RootUncaptured m)
    (hmain : closureMainB κ I = true) (ht : activationReturnB Γc = true)
    (fresh : origin.frames.size ≤ m.stack.headD 0)
    (hcaller : Framed origin (popMethodFrame m)) (h : Framed m n)
    (hn : StateOk (callbackMethodCtx κ fr code) Γm I n) :
    StateOk κ Γc I (popMethodFrame n) := by
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hmain
  obtain ⟨hr, hw, hclass, hasm, hself, hblock, hconst, hi⟩ := hmain
  have hou : RootUncaptured origin := by
    rw [RootUncaptured, rootFrame_eq_currentFrame ho.frameInRange.1]
    exact (ho.runtime hr).captured
  have hcu : RootUncaptured (popMethodFrame m) := by
    rw [RootUncaptured, rootFrame_eq_currentFrame hc.frameInRange.1]
    exact (hc.runtime hr).captured
  have hf := method_ordinary_project ho.frameInRange hou hu fresh hcaller h
  have heq := ordinary_caller_frame h hu hc.frameInRange (by
    rw [hcaller.stack]
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le ho.frameInRange.2 fresh))
  have hrange : FrameInRange (popMethodFrame n) :=
    ⟨by rw [hf.stack]; exact ho.frameInRange.1,
      by rw [hf.stack]; exact Nat.lt_of_lt_of_le ho.frameInRange.2 hf.frames.size⟩
  have move {τ : Ty} {v : Value} (ht : activationStableB τ = true)
      (hv : denM τ (popMethodFrame m) v) : denM τ (popMethodFrame n) v :=
    activationStable_heap (m := n) ht rfl
      (activationStable_framed ht h (activationStable_heap (m := popMethodFrame m) ht rfl hv))
  have henv := hc.env.reframe_uncaptured hc.frameInRange hrange hcu heq
    (fun p hp _ hv => move (List.all_eq_true.mp ht p hp) hv)
  have hframe : FrameOk κ.frame (popMethodFrame n) := by
    cases hf' : κ.frame with
    | none => simpa only [FrameOk, hf', heq] using hc.frame
    | some f =>
      have old : FrameOk (some f) (popMethodFrame m) := by simpa only [hf'] using hc.frame
      refine ⟨by rw [heq]; exact old.1, ?_, by rw [heq]; exact old.2.2⟩
      rw [heq]
      exact move (by unfold activationStableB Frame.recvTy; split <;> rfl) old.2.1
  have hscope := hf.frames.scope
  rw [rootFrame_eq_currentFrame hrange.1, rootFrame_eq_currentFrame ho.frameInRange.1] at hscope
  have hctx : returnScopeCtx κ (callbackMethodCtx κ fr code) = κ := by cases κ; rfl
  have hout := restore_main_state_atStack_frame (κb := callbackMethodCtx κ fr code) (s := n.stack.tail) ho
    (hctx.symm ▸ ReframeFO.empty hi hself hblock hconst) hasm hr hw hclass
    (fun x => (constGet?_empty (κ := callbackMethodCtx κ fr code) hconst x).trans
      (constGet?_empty (κ := returnScopeCtx κ (callbackMethodCtx κ fr code)) hconst x).symm)
    hf hscope hframe henv (hf.phase.trans (ho.runtime hr).phase) hn
  simpa only [hctx, popMethodFrame] using hout

/-- Ordinary dispatch and expressions share the same caller-restoration boundary. -/
theorem RunSpec.methodOrdinary {origin m start : Machine} {κ : Ctx} {Γ₀ Γc Γm' : Env}
    {I τ : Ty} {fr : Ratchet.Frame} {code : ClosureCode}
    (h : RunSpec m start Γm' τ (callbackMethodCtx κ fr code) I)
    (ho : StateOk κ Γ₀ I origin) (hc : StateOk κ Γc I (popMethodFrame m))
    (hu : RootUncaptured m)
    (hmain : closureMainB κ I = true) (ht : activationReturnB Γc = true)
    (fresh : origin.frames.size ≤ m.stack.headD 0)
    (hcaller : Framed origin (popMethodFrame m)) :
    MethodRunSpec m start Γc Γm' τ κ (callbackMethodCtx κ fr code) I I := by
  refine ⟨h.1, ?_⟩
  intro fuel a n rest he
  have hn := h.2 fuel a n rest he
  refine ⟨.ordinary hn.1, hn.2.1, ?_⟩
  intro v hv
  exact ⟨ordinary_caller_state ho hc hu hmain ht fresh hcaller hn.1
    (hn.2.2 v hv), hn.2.2 v hv⟩

/-- Reuse ordinary expression typing inside a callback-capable method. Method-local
flow changes remain allowed; the caller retains stable capture types. Sorbet 0.6.13405
accepts `first=nil; first=yield(1)` with an Integer callback (clinks 232–233). -/
theorem SemSafeCtxA.methodOrdinary {origin m : Machine} {κ : Ctx} {Γ₀ Γc Γm Γm' : Env}
    {I τ : Ty} {fr : Ratchet.Frame} {code : ClosureCode} {e : Ratchet.Expr}
    (h : SemSafeCtxA (callbackMethodCtx κ fr code) Γm I e τ
      (callbackMethodCtx κ fr code) Γm' I)
    (ho : StateOk κ Γ₀ I origin) (hc : StateOk κ Γc I (popMethodFrame m))
    (hm : StateOk (callbackMethodCtx κ fr code) Γm I m) (hu : RootUncaptured m)
    (hmain : closureMainB κ I = true) (ht : activationReturnB Γc = true)
    (fresh : origin.frames.size ≤ m.stack.headD 0)
    (hcaller : Framed origin (popMethodFrame m)) :
    MethodRunSpec m (evalFrom m e) Γc Γm' τ κ (callbackMethodCtx κ fr code) I I :=
  (h m hm).methodOrdinary ho hc hu hmain ht fresh hcaller

/-- The callback result restores both frames, including stable method locals and its
actual block. It therefore embeds into the same effect target as ordinary expressions. -/
theorem CallbackResultOk.methodResult {m n : Machine} {κ : Ctx} {Γc Γm : Env} {I τ : Ty}
    {fr : Ratchet.Frame} {code : ClosureCode} {a : Answer}
    (h : CallbackResultOk m Γc τ κ I a n)
    (hc : StateOk κ Γc I (popMethodFrame m))
    (hm : StateOk (callbackMethodCtx κ fr code) Γm I m)
    (hmain : closureMainB κ I = true) (hs : CallbackMethodScope m)
    (ht : activationReturnB Γm = true) :
    MethodResultOk m Γc Γm τ κ (callbackMethodCtx κ fr code) I I a n := by
  refine ⟨.callback h.1, h.2.1, ?_⟩
  intro v hv
  subst a
  exact ⟨h.2.2 v rfl, h.methodState hc hm hmain hs ht⟩

#print axioms ordinary_caller_state
#print axioms RunSpec.methodOrdinary
#print axioms SemSafeCtxA.methodOrdinary
#print axioms CallbackResultOk.methodResult
end Ratchet.Denote.Typed
