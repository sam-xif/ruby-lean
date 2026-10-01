import Denote.Rules.Method.CallbackState

/-! Method bodies compose ordinary expression effects with callback effects. Ordinary
expressions may write method locals; callbacks may write captured caller locals. Sorbet
0.6.13405 accepts both in one method (clink 232). The original caller predates allocation
of the method frame, so its return contract must not freeze that fresh frame's locals. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Closure under composition of the two already certified effect boundaries. This is
a semantic effect relation, not a new source typing rule or a relaxation of Framed. -/
inductive MethodEffects : Machine → Machine → Prop where
  | ordinary {m n : Machine} : Framed m n → MethodEffects m n
  | callback {m n : Machine} : CallbackFramed m n → MethodEffects m n
  | trans {m n out : Machine} : MethodEffects m n → MethodEffects n out → MethodEffects m out

theorem MethodEffects.refl (m : Machine) : MethodEffects m m := .ordinary (.refl m)

theorem MethodEffects.stack {m n : Machine} (h : MethodEffects m n) : n.stack = m.stack := by
  induction h with
  | ordinary h => exact h.stack
  | callback h => exact h.stack
  | trans _ _ ih ih' => exact ih'.trans ih

theorem MethodEffects.size {m n : Machine} (h : MethodEffects m n) : m.frames.size ≤ n.frames.size := by
  induction h with
  | ordinary h => exact h.frames.size
  | callback h => exact h.caller.frames.size
  | trans _ _ ih ih' => exact Nat.le_trans ih ih'

theorem MethodEffects.inRange {m n : Machine} (h : MethodEffects m n)
    (hm : FrameInRange m) : FrameInRange n :=
  ⟨by rw [h.stack]; exact hm.1, by rw [h.stack]; exact Nat.lt_of_lt_of_le hm.2 h.size⟩

theorem MethodEffects.scope {m n : Machine} (h : MethodEffects m n) (hm : FrameInRange m) :
    frameScope n.currentFrame = frameScope m.currentFrame := by
  induction h with
  | @ordinary m n h =>
    have hs := h.frames.scope
    rw [rootFrame_eq_currentFrame (m := n) (by rw [h.stack]; exact hm.1),
      rootFrame_eq_currentFrame hm.1] at hs
    exact hs
  | callback h => exact congrArg frameScope h.active
  | trans h _ ih ih' => exact (ih' (h.inRange hm)).trans (ih hm)

theorem MethodEffects.uncaptured {m n : Machine} (h : MethodEffects m n)
    (hm : FrameInRange m) (hu : RootUncaptured m) : RootUncaptured n := by
  rw [RootUncaptured, rootFrame_eq_currentFrame (h.inRange hm).1]
  rw [RootUncaptured, rootFrame_eq_currentFrame hm.1] at hu
  exact (congrArg FrameScope.captured (h.scope hm)).trans hu

theorem MethodEffects.firstOrder {m n : Machine} (h : MethodEffects m n)
    {τ : Ty} (ht : FirstOrder τ = true) {v : Value} (hv : denM τ m v) : denM τ n v := by
  induction h with
  | ordinary h => exact h.firstOrder τ ht v hv
  | callback h => exact h.stable (by simp only [activationStableB, ht, Bool.true_or]) hv
  | trans _ _ ih ih' => exact ih' (ih hv)

theorem MethodEffects.procs {m n : Machine} (h : MethodEffects m n) : ProcPres m.heap n.heap := by
  induction h with
  | ordinary h => exact h.procs
  | callback h => exact h.caller.procs
  | trans _ _ ih ih' => exact ih.trans ih'

/-- Continue an existing caller frame contract when only frames allocated after that
caller entry may have changed. Existing caller-local changes in h remain permitted. -/
private theorem framePres_prefix {origin m n : Machine}
    (hl : FrameInRange origin) (hu : RootUncaptured origin)
    (h : FramePres origin m) (hs : m.stack = origin.stack) (hs' : n.stack = m.stack)
    (hz : m.frames.size ≤ n.frames.size)
    (hf : ∀ i, i < origin.frames.size → n.frames.getD i default = m.frames.getD i default) :
    FramePres origin n := by
  have hscope : frameScope (n.frames.getD (n.stack.headD 0) default) =
      frameScope (origin.frames.getD (origin.stack.headD 0) default) := by
    rw [hs', hf _ (by rw [hs]; exact hl.2)]
    exact h.scope
  refine ⟨Nat.le_trans h.size hz, hscope, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc i hi hn; exact (hf i hi).trans (h.isolated hc i hi hn)
  · intro i hi hn; exact (congrArg savedFrame (hf i hi)).trans (h.saved i hi hn)
  · intro hc i hi hn; exact (hf i hi).trans (h.outside hc i hi hn)
  · refine ⟨?_, ?_⟩
    · intro i hi x hx
      simpa only [frameBinds, hf i hi] using h.bindings.bound i hi x hx
    · intro i hi hn x
      simpa only [frameBinds, hf i hi] using h.bindings.saved i hi hn x
  · exact OwnersPres.uncaptured (hs'.trans hs) hu ((congrArg FrameScope.captured hscope).trans hu)
  · intro x hx i hi hn
    rw [hf i hi]
    exact h.shadows x hx i hi hn

/-- Ordinary method-local writes preserve the original caller's frame contract because
the active method id is newer than every frame mentioned by that contract. -/
theorem method_ordinary_project {origin m n : Machine}
    (hl : FrameInRange origin) (hu : RootUncaptured origin) (hm : RootUncaptured m)
    (fresh : origin.frames.size ≤ m.stack.headD 0)
    (hcaller : Framed origin (popMethodFrame m)) (h : Framed m n) :
    Framed origin (popMethodFrame n) := by
  have hs : (popMethodFrame n).stack = (popMethodFrame m).stack := by
    simp only [popMethodFrame, h.stack]
  refine ⟨hs.trans hcaller.stack, fun k hk => h.cls k (hcaller.cls k hk),
    fun v cn hv => h.nominal v cn (hcaller.nominal v cn hv), ?_, ?_,
    hcaller.fields.trans (h.fields.reheap rfl rfl), ?_, hcaller.procs.trans h.procs,
    h.phase.trans hcaller.phase⟩
  · intro τ ht v hv
    have hv' := (denM_heap_only (m₁ := popMethodFrame m) (m₂ := m) ht rfl).mp
      (hcaller.firstOrder τ ht v hv)
    exact (denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) ht rfl).mp (h.firstOrder τ ht v hv')
  · apply framePres_prefix hl hu hcaller.frames hcaller.stack hs h.frames.size
    intro i hi
    exact h.frames.isolated hm i (Nat.lt_of_lt_of_le hi hcaller.frames.size)
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le hi fresh))
  · intro o ho e he
    exact h.cachedEigen o (Nat.lt_of_lt_of_le ho hcaller.fields.size) e (hcaller.cachedEigen o ho e he)

/-- The shared return theorem for a method mixing local assignments and callbacks.
The caller is anchored before method allocation; no preservation of the fresh method's
locals is claimed. All old caller frames retain the original certified Framed contract. -/
theorem MethodEffects.project {m n : Machine} (h : MethodEffects m n)
    {origin : Machine} (hl : FrameInRange origin) (hu : RootUncaptured origin)
    (hm : FrameInRange m) (hmu : RootUncaptured m)
    (fresh : origin.frames.size ≤ m.stack.headD 0)
    (hcaller : Framed origin (popMethodFrame m)) : Framed origin (popMethodFrame n) := by
  induction h with
  | ordinary h => exact method_ordinary_project hl hu hmu fresh hcaller h
  | callback h => exact hcaller.trans h.caller
  | trans h _ ih ih' =>
    exact ih' (h.inRange hm) (h.uncaptured hm hmu) (by rw [h.stack]; exact fresh)
      (ih hm hmu fresh hcaller)

#print axioms MethodEffects.project
#print axioms MethodEffects.firstOrder
end Ratchet.Denote.Typed
