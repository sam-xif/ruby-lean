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

/-- The `methodIn` twin of `procClosure_alloc`, for the same reason one layer over:
`enterUserMethod` can allocate (a keyword bundle, a rest array) **before** it pushes the method
frame, so the `Sealed.meth` fact its push premise needs has to cross that allocation. The
in-range side condition is derivable the same way — `classPayload?` of an out-of-range read is
`none`, because `default.payload` is `.none`. -/
theorem methodIn_lt {h : Heap} {k : ObjId} {n : String} {md : MethodDef}
    (hmd : methodIn h k n = some md) : k < h.objs.size := by
  rcases Nat.lt_or_ge k h.objs.size with hlt | hge
  · exact hlt
  · rw [methodIn, Heap.classPayload?, heap_get_oob hge,
      show (default : Object).payload = Payload.none from rfl] at hmd
    exact absurd hmd (by simp)

theorem methodIn_alloc {h : Heap} {k : ObjId} {n : String} {md : MethodDef} (obj : Object)
    (hmd : methodIn h k n = some md) : methodIn (h.alloc obj).2 k n = some md := by
  rw [methodIn, Heap.classPayload?, alloc_get_lt obj (methodIn_lt hmd), ← Heap.classPayload?,
    ← methodIn]
  exact hmd

#print axioms procClosure_lt
#print axioms procClosure_alloc
#print axioms methodIn_alloc

/-! ### `callClosure` — the first frame-pusher, and its push premise is a *heap* fact

`Sealed.clos` at the closure being invoked is exactly what covers the push, which is what that
clause exists for (the eighteenth stall point's enumeration). Three shapes in the body: two
`.unsupported` gates (not `.next`, so refuted), the arity `raiseErr`, and the main path — which
on the rest-parameter branch **allocates before it pushes**, so `procClosure_alloc` carries the
heap fact across.

**Correction to an earlier diagnosis, recorded because it cost three lemmas.** This was parked
on the grounds that `split at hstep` cannot peel `Interp/`'s chains. That is **false** —
`set_option trace.split.failure true` reports no failure here, and `split at hstep` peels this
body fine. What went wrong the first time was *ordering*: closers that ran before `split` and
searched instead of peeling. `Builtins` was not the wrong sample after all; the closer list was
in the wrong order. -/

set_option maxHeartbeats 4000000 in
theorem Step.callClosure {b : FrameId} {m m' : Machine} (h : StepInv b m) {o : ObjId}
    {cl : Closure} (hcl : procClosure? m.heap (.ref o) = some cl) (args : List Value)
    (brk : Option FrameId) (selfOv : Option Value) (defmodOv : Option ObjId)
    (hstep : Interp.callClosure m cl args brk selfOv defmodOv = .next m') : Step b m m' := by
  rw [Interp.callClosure] at hstep
  dsimp only at hstep
  repeat (any_goals (first
    -- peel first: this is the ordering the first attempt got wrong
    | split at hstep
    | (cases hstep; exact Step.raiseErr h _ _)
    | (cases hstep
       refine Step.withKont' ?_ _ _
       exact Step.push_clos h _ hcl rfl)
    -- `o` and `cl` are implicit and appear only in `hcl`, so it has to be supplied
    -- directly rather than left as `?_` -- otherwise they are unsolvable at that point
    | (cases hstep
       refine Step.withKont' ?_ _ _
       refine Step.push_clos' ?_ _ (procClosure_alloc _ hcl) rfl
       exact Step.allocArr h _)
    | (dsimp only at hstep)
    -- the two `.unsupported` gates, refuted **by rewriting the hypothesis**. `exact absurd
    -- hstep (by simp)` is wrong here and wrong subtly: the `by simp` is postponed, so the
    -- `exact` succeeds, this alternative wins, and the correct closers never run -- 70 stray
    -- `¬ …` goals surface at the end instead. A refutation in a `first` chain must act on the
    -- hypothesis, not park a term-level side goal.
    | (simp at hstep)))

#print axioms Step.callClosure

/-! ### `appendKwHash` and `enterHandler` — the two remaining allocation/write helpers -/

/-- **`appendKwHash`** — either the identity or one `Hash` allocation. -/
theorem Step.appendKwHash {b : FrameId} {m : Machine} (h : StepInv b m) (args : List Value)
    (kw : List (Value × Value)) : Step b m (Interp.appendKwHash m args kw).2 := by
  unfold Interp.appendKwHash
  split
  · exact Step.refl h
  · exact Step.allocHsh h _

/-! **`enterHandler`** — sets `$!`, binds the `=> x` target in whichever of the five ways the
target names, then `withKont`. `lvar` is `Step.setLocal'`, `gvar` is `Step.setGlobal'` (which is
what forced `Step.setLastMatchValue`), `ivar` is `Step.bindIvar`, `const` is a `constSet` — a
`setClassPayload` that rewrites `consts` and leaves `methods`, so
`CapMono.setClassPayload_methods` is its shape — and `cvar` is the identity. -/

set_option maxHeartbeats 2000000 in
theorem Step.enterHandler {b : FrameId} {m : Machine} (h : StepInv b m) (node : RubyCore.BeginNode)
    (exc : Value) (ref : Option (RubyCore.TargetKind × String)) (handler : RubyCore.Expr) :
    Step b m (Interp.enterHandler m node exc ref handler) := by
  unfold Interp.enterHandler
  have h0 : Step b m { m with currentExc := some exc } := Step.frameOnly h rfl rfl rfl
  refine Step.withKont' ?_ _ _
  repeat (any_goals (first
    | split
    | exact h0
    | refine Step.setLocal' h0 _ _
    | refine Step.setGlobal' h0 _ _
    | exact h0.trans (Step.bindIvar h0.2 _ _)
    -- the `MCap` goal `heap'` leaves has to reach the *outer* fixpoint, because `constSet`
    -- carries its own `match classPayload?` and needs this list's `split`
    | refine Step.heap' h0 rfl rfl ?_
    | exact MCap.of_eq rfl
    | exact MCap.set_payload_eq rfl rfl
    | exact CapMono.setClassPayload_methods (by assumption) rfl
    -- `constSet` is a *call*: proved once as `CapMono.constSet` rather than unfolded inside
    -- this fixpoint, which is the kind of guessing that costs a run
    | exact CapMono.of_constSet _ _ _))

#print axioms Step.enterHandler

#print axioms Step.appendKwHash

#print axioms Step.bindIvar
#print axioms Step.reifyBlock
#print axioms Step.doReturn
#print axioms Step.finishRegion

end Ratchet.Denote
