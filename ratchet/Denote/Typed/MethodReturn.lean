import Denote.Typed.MethodEntry

/-! Recover the caller's frame and locals from the strengthened body contract.
Captured callers need an additional captured-chain transport, not an assumed equality.
-/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def popMethodFrame (m : Machine) : Machine := { m with stack := m.stack.tail }

theorem method_frame_savedFrames {m n : Machine} {f : RubyCore.Frame}
    (hc : f.captured = none) (h : FramePres (pushMethodFrame m f) n) :
    ∀ i, i < m.frames.size → n.frames.getD i default = m.frames.getD i default := by
  have hu : RootUncaptured (pushMethodFrame m f) := by
    simp [RootUncaptured, pushMethodFrame, Array.getD_eq_getD_getElem?, hc]
  intro i hi
  have hs := h.isolated hu i
    (by simpa [pushMethodFrame] using Nat.lt_succ_of_lt hi)
    (by simpa [pushMethodFrame] using Nat.ne_of_lt hi)
  have hr : (m.frames.push f).getD i default = m.frames.getD i default := by
    simp [Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt]
  simpa only [pushMethodFrame, hr] using hs

theorem method_savedFrames {m n : Machine} {f : RubyCore.Frame}
    (hc : f.captured = none) (h : Framed (pushMethodFrame m f) n) :
    ∀ i, i < m.frames.size → n.frames.getD i default = m.frames.getD i default :=
  method_frame_savedFrames hc h.frames

/-- Frame restoration is independent of any claim that the body preserves heap types. -/
theorem method_frame_pop {m n : Machine} {f : RubyCore.Frame}
    (hl : m.stack.headD 0 < m.frames.size) (hc : f.captured = none)
    (hb : n.stack = (pushMethodFrame m f).stack) (h : FramePres (pushMethodFrame m f) n) :
    FramePres m (popMethodFrame n) := by
  have hs : (popMethodFrame n).stack = m.stack := by
    simp [popMethodFrame, hb, pushMethodFrame]
  have hf := method_frame_savedFrames hc h
  refine ⟨?_, ?_, ?_⟩
  · have hh := h.size
    simp only [pushMethodFrame, Array.size_push] at hh
    exact Nat.le_trans (Nat.le_succ _) hh
  · change frameScope ((popMethodFrame n).frames.getD ((popMethodFrame n).stack.headD 0) default) = _
    rw [hs]
    exact congrArg frameScope (hf _ hl)
  · intro _ i hi _
    exact hf i hi

theorem method_pop_framed {m n : Machine} {f : RubyCore.Frame}
    (hl : m.stack.headD 0 < m.frames.size) (hc : f.captured = none)
    (h : Framed (pushMethodFrame m f) n) : Framed m (popMethodFrame n) := by
  refine ⟨by simp [popMethodFrame, h.stack, pushMethodFrame], h.cls, h.nominal, ?_,
    method_frame_pop hl hc h.stack h.frames⟩
  intro τ ht v hv
  have he : denM τ (pushMethodFrame m f) v :=
    (denM_heap_only (m₁ := m) (m₂ := pushMethodFrame m f) ht rfl).mp hv
  exact (denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) ht rfl).mp
    (h.firstOrder τ ht v he)

private theorem getLocal_uncaptured {m : Machine} (hc : RootUncaptured m) (x : String) :
    m.getLocal x = (((m.frames.getD (m.stack.headD 0) default).locals.find?
      (·.1 == x)).map (·.2)).getD .nil := by
  unfold RootUncaptured at hc
  simp only [Machine.getLocal, Machine.getLocal.go]
  cases hs : (m.frames.getD (m.stack.headD 0) default).locals.find? (·.1 == x) with
  | none => rw [hc]; rfl
  | some p => cases p; rfl

theorem method_pop_getLocal {m n : Machine} {f : RubyCore.Frame}
    (hl : m.stack.headD 0 < m.frames.size) (hu : RootUncaptured m)
    (hc : f.captured = none) (h : Framed (pushMethodFrame m f) n) (x : String) :
    (popMethodFrame n).getLocal x = m.getLocal x := by
  have hp := method_pop_framed hl hc h
  have hn : RootUncaptured (popMethodFrame n) := hp.frames.rootCaptured.trans hu
  rw [getLocal_uncaptured hn, getLocal_uncaptured hu]
  change (((n.frames.getD ((popMethodFrame n).stack.headD 0) default).locals.find?
    (·.1 == x)).map (·.2)).getD .nil = _
  rw [hp.stack, method_savedFrames hc h _ hl]

/-- Ordinary callers recover their local environment; first-order local types retain
their denotations through the body, and aliases retain their actual value equality. -/
theorem method_pop_envOk {m n : Machine} {f : RubyCore.Frame} {Γ : Env}
    (hl : m.stack.headD 0 < m.frames.size) (hu : RootUncaptured m)
    (hc : f.captured = none) (h : Framed (pushMethodFrame m f) n)
    (he : EnvOk Γ m) (ht : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) :
    EnvOk Γ (popMethodFrame n) := by
  have hp := method_pop_framed hl hc h
  have hv := method_pop_getLocal hl hu hc h
  constructor
  · intro x τ hx
    obtain ⟨z, hz⟩ := envGet?_mem hx
    obtain ⟨hd, ha⟩ := he.1 x τ hx
    refine ⟨?_, ?_⟩
    · rw [hv]
      exact hp.firstOrder _ (ht (z, τ) hz) _ hd
    · intro y ρ hy
      rw [hv, hv]
      exact ha y ρ hy
  · intro x hx
    rw [hv]
    exact he.2 x hx

theorem step_frameK_value (n : Machine) (fid : FrameId) (v : Value) :
    Interp.stepFn (deliverA (.val v) n [.frameK fid]) =
      .next (deliverA (.val v) (popMethodFrame n) []) := rfl

private theorem frameK_escape {origin n : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    (fid : FrameId) (j : Jump) (he : EscOk n j)
    (hr : RunSpec origin (deliverA (.esc j) (popMethodFrame n) []) Γ τ κ I) :
    RunSpec origin (deliverA (.esc j) n [.frameK fid]) Γ τ κ I := by
  cases j with
  | retJ => cases he
  | throwJ => cases he
  | raiseJ exc => exact RunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl) hr
  | brkJ v | nxtJ v | redoJ | retryJ =>
    by_cases hc : (n.frames[fid]?.getD default).kind = .classBody
    · apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from ?_) hr
      simp [Interp.stepFn, deliverA, Answer.ctl, Interp.unwind, hc,
        Interp.withCtl, popMethodFrame]
    · apply RunSpec.unsupported (msg := "break/next/retry/redo crossing a method boundary") (by rfl)
      simp [Interp.stepFn, deliverA, Answer.ctl, Interp.unwind, hc]

/-- The return continuation depends only on the delivered answer, not on an unbounded
body hypothesis. Bounded and unbounded method entry share this proof. -/
theorem methodFrame_continue_spec {m : Machine} {f : RubyCore.Frame}
    {Γb Γ : Env} {κb κ : Ctx} {Ib I τ : Ty}
    (hl : m.stack.headD 0 < m.frames.size) (hc : f.captured = none)
    (ht : FirstOrder τ = true)
    (hs : ∀ n v, ResultOk (pushMethodFrame m f) Γb τ (.val v) n κb Ib →
      StateOk κ Γ I (popMethodFrame n))
    {a : Answer} {n : Machine} (hr : ResultOk (pushMethodFrame m f) Γb τ a n κb Ib) :
    RunSpec m (deliverA a n [.frameK m.frames.size]) Γ τ κ I := by
  have hf := method_pop_framed hl hc hr.1
  cases a with
  | val v =>
    apply RunSpec.step (by rfl) (step_frameK_value n _ v)
    exact RunSpec.answer ⟨hf,
      (denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) ht rfl).mp hr.2.1,
      fun _ _ => hs n v hr⟩
  | esc j =>
    apply frameK_escape _ j hr.2.1
    apply RunSpec.answer
    refine ⟨hf, ?_, fun _ hv => by cases hv⟩
    cases j <;> exact hr.2.1

/-- Consume a checked body at its method frame and return an answer at the caller.
The conformance premise is explicit; `MethodState.lean` discharges it rather than
manufacturing the caller's `StateOk` from its local environment alone. Method-return jumps require the
future answer contract's return arm; the current body contract excludes them. -/
theorem methodFrame_runSpec {m : Machine} {f : RubyCore.Frame} {e : Ratchet.Expr}
    {Γb Γ : Env} {κb κ : Ctx} {Ib I τ : Ty}
    (hl : m.stack.headD 0 < m.frames.size) (hc : f.captured = none)
    (ht : FirstOrder τ = true)
    (hb : RunSpec (pushMethodFrame m f) (evalFrom (pushMethodFrame m f) e) Γb τ κb Ib)
    (hs : ∀ n v, ResultOk (pushMethodFrame m f) Γb τ (.val v) n κb Ib →
      StateOk κ Γ I (popMethodFrame n)) :
    RunSpec m (pushK [.frameK m.frames.size] (evalFrom (pushMethodFrame m f) e)) Γ τ κ I := by
  apply hb.bindSpec (by
    intro k hk tag
    simp only [List.mem_singleton] at hk
    subst hk
    simp)
  intro a n hr
  exact methodFrame_continue_spec hl hc ht hs hr

#print axioms method_pop_envOk
#print axioms methodFrame_runSpec
end Ratchet.Denote.Typed
