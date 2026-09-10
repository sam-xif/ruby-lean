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

/-! ### `procClosure?` survives an allocation, which `callClosure` needs about itself

`callClosure`'s rest-parameter path calls `allocArr` **before** it pushes the block frame, so the
heap fact its push premise needs (`Sealed.clos` at the closure being invoked) has to be carried
across that allocation. Note the in-range side condition is *derivable* rather than assumed: a
`procClosure?` that answers `some` cannot be reading past the end of the heap, because
`Heap.get`'s out-of-range answer is `default`, whose payload is `.none`. -/

/-- Reading past the end of the heap answers `default`, whose payload is `.none`. Mirrors
`alloc_get_gt`'s shape (`simp only` for the projections, `rw` for the array lemmas). -/
theorem heap_get_oob {h : Heap} {o : ObjId} (ho : h.objs.size ≤ o) : h.get o = default := by
  simp only [Heap.get]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none ho, Option.getD_none]

theorem procClosure_lt {h : Heap} {o : ObjId} {cl : Closure}
    (hcl : procClosure? h (.ref o) = some cl) : o < h.objs.size := by
  rcases Nat.lt_or_ge o h.objs.size with hlt | hge
  · exact hlt
  · rw [procClosure?, heap_get_oob hge,
      show (default : Object).payload = Payload.none from rfl] at hcl
    exact absurd hcl (by simp)

theorem procClosure_alloc {h : Heap} {o : ObjId} {cl : Closure} (obj : Object)
    (hcl : procClosure? h (.ref o) = some cl) :
    procClosure? (h.alloc obj).2 (.ref o) = some cl := by
  rw [procClosure?, alloc_get_lt obj (procClosure_lt hcl), ← procClosure?]
  exact hcl

#print axioms procClosure_lt
#print axioms procClosure_alloc

/-! ### `callClosure`, parked — and the obstruction is `split`, not the seal

Its push premise is **already discharged**: `Step.push_clos` plus `procClosure_alloc` above give
`callClosure` everything it needs about the heap, and the first `ite` peels by hand exactly as
`doReturn`'s does. What blocks it is mechanical: the body is **five nested `ite`s**, `split at h`
cannot peel any of them (measured — it fails in under a second, the same way it fails on
`doReturn`'s `have`-bound target), and **`split_ifs` is Mathlib-only and not in this package's
dependency set** (checked). So each condition has to be transcribed by hand, and two of them
(`autoSplat`, `arityOk`) are defined through a `let`-chain over `classifySimple`'s result — the
`newImpl_locals` situation, which `FrameLocal.lean` solved by naming the payload and peeling the
`if`s by hand across ~15 lines.

That is ordinary work and it is *not* on the critical path for anything else in stage 1, so it is
recorded here rather than half-done. Nothing above depends on it. -/

/-! ### `appendKwHash` and `enterHandler` — the two remaining allocation/write helpers -/

/-- **`appendKwHash`** — either the identity or one `Hash` allocation. -/
theorem Step.appendKwHash {b : FrameId} {m : Machine} (h : StepInv b m) (args : List Value)
    (kw : List (Value × Value)) : Step b m (Interp.appendKwHash m args kw).2 := by
  unfold Interp.appendKwHash
  split
  · exact Step.refl h
  · exact Step.allocHsh h _

/-! ### `enterHandler`, parked with `callClosure` — and for a related reason

Four of its five target arms close (`lvar` by `Step.setLocal'`, `gvar` by `Step.setGlobal'`
— which is what forced `Step.setLastMatchValue` above — `ivar` by `Step.bindIvar`, `cvar` by
identity). The `const` arm is a `Heap.constSet`, which is a `setClassPayload` that rewrites
`consts` and leaves `methods`, so `CapMono.setClassPayload_methods` is exactly its shape — but
`constSet` carries its *own* `match h.classPayload? Object`, and getting the split and the
`by assumption` for the payload lookup to line up inside a fixpoint is the same mechanical
problem `callClosure` has. Recorded rather than half-done; nothing else in stage 1 depends on it. -/

#print axioms Step.appendKwHash

#print axioms Step.bindIvar
#print axioms Step.reifyBlock
#print axioms Step.doReturn
#print axioms Step.finishRegion

end Ratchet.Denote
