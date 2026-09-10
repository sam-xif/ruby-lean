import Denote.Sem.StepEval

/-!
# `Denote/Sem/StepSupport.lean` — stage 1 of the walk: `Interp/Support.lean`

`Denote/Sem/StepEval.lean` records the five-stage bottom-up order the walk has to be built in,
measured the hard way. This is stage 1: the helpers `evalExpr`, `applyKont` and the dispatchers
all call, each getting one `Step` lemma so its callers close with an `exact`.

The vocabulary is `StepInterp.lean`'s, and the one that does the work is **`Step.heap`** — any
capture-monotone heap change — discharged by the `MCap` closers the `Builtins` walk already
measured. That is why there is no `Step.bindIvar`-shaped lemma per helper: `bindIvar` *is* a
`Heap.set` with the payload copied, which is `MCap.set_payload_eq rfl rfl`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

/-- **`bindIvar`** — a `Heap.set` that rewrites `ivars` and copies the payload, so it carries no
new capture edge. The `self`-is-an-immediate arm is the identity. -/
theorem Step.bindIvar {b : FrameId} {m : Machine} (h : StepInv b m) (x : String) (v : Value) :
    Step b m (Interp.bindIvar m x v) := by
  unfold Interp.bindIvar
  split
  · exact Step.heap h rfl rfl (MCap.set_payload_eq rfl rfl)
  · exact Step.refl h

/-- **`reifyBlock`** — the one allocation in this layer that installs a *capturing* closure. Its
`captured` is `m.stack.headD 0`, the current frame, which `FramesWF.nonEmpty` puts on the stack,
so `Sealed.stack` at that frame discharges `Sealed.alloc`'s premise. This is the row the
eighteenth stall point's enumeration called "free already", and it is the reason the seal pays
for its own closures. -/
theorem Step.reifyBlock {b : FrameId} {m : Machine} (h : StepInv b m) (params : List RubyCore.Param)
    (locals : List String) (body : RubyCore.Expr) (lam : Bool) :
    Step b m (Interp.reifyBlock m params locals body lam).2 := by
  refine ⟨rfl, ?_⟩
  refine { sealed := ?_, wf := ?_, inRange := h.inRange }
  · refine h.sealed.alloc _ (fun cl hp p hcap => ?_) (fun cp hp _ _ _ _ _ => absurd hp (by simp))
    -- the closure captured the current frame, and the current frame is on the stack
    simp only [Payload.proc.injEq] at hp
    subst hp
    simp only [Option.some.injEq] at hcap
    subst hcap
    exact h.sealed.stack _ (by
      cases hs : m.stack with
      | nil => exact absurd hs h.wf.nonEmpty
      | cons a rest => simp [hs, List.headD])
  · refine h.wf.alloc _ (fun cl hp p hcap => ?_) (fun cp hp _ _ _ _ _ => absurd hp (by simp))
    simp only [Payload.proc.injEq] at hp
    subst hp
    simp only [Option.some.injEq] at hcap
    subst hcap
    exact h.wf.stack _ (by
      cases hs : m.stack with
      | nil => exact absurd hs h.wf.nonEmpty
      | cons a rest => simp [hs, List.headD])

/-- **`doReturn`** — either a `ctl` write or a `raiseErr`, both already keyed. -/
theorem Step.doReturn {b : FrameId} {m m' : Machine} (h : StepInv b m) (v : Value)
    (hstep : Interp.doReturn m v = .next m') : Step b m m' := by
  unfold Interp.doReturn at hstep
  dsimp only at hstep
  by_cases hc : m.stack.contains (Interp.returnTarget m) = true
  · rw [if_pos hc] at hstep
    cases hstep; exact Step.withCtl h _
  · rw [if_neg hc] at hstep
    cases hstep; exact Step.raiseErr h _ _

/-- **`finishRegion`** — four arms, every one a `ctl`/`kont`/`currentExc` write. -/
theorem Step.finishRegion {b : FrameId} {m : Machine} (h : StepInv b m) (ens : Option RubyCore.Expr)
    (pending : RubyCore.Pending) : Step b m (Interp.finishRegion m ens pending) := by
  unfold Interp.finishRegion
  repeat (any_goals (first
    | exact Step.withCtl h _
    | exact Step.withKont h _ _
    | exact Step.frameOnly h rfl rfl rfl
    | split))

#print axioms Step.bindIvar
#print axioms Step.reifyBlock
#print axioms Step.doReturn
#print axioms Step.finishRegion

end Ratchet.Denote
