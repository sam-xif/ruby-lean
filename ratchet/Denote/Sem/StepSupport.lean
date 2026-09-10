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

/-! ### `destructureBind` — a fuel recursion with two folds, and the folds recurse

`def f((a, b), c)`. Two folds over `bindPos`, which for a nested `.destr` sub-parameter calls
`destructureBind` again at lower fuel; between them, a rest sub-parameter allocates an array.
So it needs a `Step`-level fold lemma first — the analogue of `foldPair_cap` for the *layer*
rather than for `MCap` — and then one induction on the fuel.

This is the helper clink 53 gave a fuel bound to (it was a `partial def`, and an opaque constant
has no equation lemmas, so nothing about it was provable at all). The bound is what makes this
induction possible. -/

theorem Step.foldPair {b : FrameId} {α β : Type} (f : β × Machine → α → β × Machine)
    (hf : ∀ (p : β × Machine) (a : α), StepInv b p.2 → Step b p.2 (f p a).2) :
    ∀ (l : List α) (p : β × Machine), StepInv b p.2 → Step b p.2 (l.foldl f p).2
  | [], p, h => Step.refl h
  | a :: rest, p, h => by
    rw [List.foldl_cons]
    exact (hf p a h).trans (Step.foldPair f hf rest (f p a) (hf p a h).2)

/-- The fold as a **peel**. Needed because a bare `have`/`Step.trans` gives the fold term no
expected type, so its list argument cannot be inferred; peeling from the outside in lets the
goal supply it at every step. -/
theorem Step.foldPair' {b : FrameId} {α β : Type} (f : β × Machine → α → β × Machine)
    (hf : ∀ (p : β × Machine) (a : α), StepInv b p.2 → Step b p.2 (f p a).2)
    (l : List α) (init : β) {m mid : Machine} (s : Step b m mid) :
    Step b m (l.foldl f (init, mid)).2 :=
  s.trans (Step.foldPair f hf l (init, mid) s.2)

/-! ### `destructureBind` — hand-split, because `split` picks the wrong match

`def f((a, b), c)`. One fuel induction over two folds, with the inner step recursing for a
nested `.destr` and a rest sub-parameter allocating between them.

**The obstruction was `split`'s *choice* of scrutinee**, not its capability. `vals` —

```lean
let vals := match v with
  | .ref o => match (m.heap.get o).payload with | .arr xs => xs.toList | _ => [v]
  | _ => [v]
```

— is **machine-irrelevant** (every branch yields the same machine) but textually precedes the
rest-parameter match the proof needs to case on, and `split` takes the first match it finds.
Splitting it yields `∀ o, v = Value.ref o → False`, which is neither dischargeable nor wanted.
`split` takes no scrutinee argument, so the remedy is to resolve the irrelevant match **by hand**
first (`cases v`, then the payload) and let the fixpoint have the relevant one. That is the same
remedy `KontFrame.lean` applies to `newImpl`, and the same one `enterUserMethod` wants. -/

theorem Step.destructureBind {b : FrameId} :
    ∀ (fuel : Nat) (m : Machine) (subs : List RubyCore.Param) (v : Value), StepInv b m →
      Step b m (Interp.destructureBind m subs v fuel).2
  | 0, m, _, _, h => Step.refl h
  | fuel + 1, m, subs, v, h => by
    -- `.eq_def`, not the bare name: the auto-generated equations for a definition with nested
    -- matches are *conditional*, and `rw [Interp.destructureBind]` leaves their discriminating
    -- side goals behind (`∀ o, v = .ref o → False`). `notes.md` tooling lesson 1.
    rw [Interp.destructureBind.eq_def]
    -- the fold's step: `.req` binds without touching the machine, `.destr` recurses at lower
    -- fuel, and the other six `Param` constructors are the identity
    have hstep : ∀ (p : List (String × Value) × Machine) (a : RubyCore.Param × Value),
        StepInv b p.2 → Step b p.2 (
          (match a.1 with
            | .req nm => (p.1 ++ [(nm, a.2)], p.2)
            | .destr subs' =>
              let r := Interp.destructureBind p.2 subs' a.2 fuel
              (p.1 ++ r.1, r.2)
            | _ => (p.1, p.2)) : List (String × Value) × Machine).2 := by
      intro p a hp
      obtain ⟨pp, val⟩ := a
      cases pp
      case destr => exact Step.destructureBind fuel p.2 _ _ hp
      all_goals exact Step.refl hp
    -- resolve `vals`'s match by hand, then peel outside-in: fold2, the rest allocation, fold1
    cases v
    case ref o =>
      cases hp : (m.heap.get o).payload
      all_goals (repeat (any_goals (first
      | (refine Step.allocArr' ?_ _; exact Step.foldPair _ hstep _ _ h)
      | exact Step.foldPair _ hstep _ _ h
      | refine Step.foldPair' _ hstep _ _ ?_
      | split)))
    all_goals (repeat (any_goals (first
      | (refine Step.allocArr' ?_ _; exact Step.foldPair _ hstep _ _ h)
      | exact Step.foldPair _ hstep _ _ h
      | refine Step.foldPair' _ hstep _ _ ?_
      | split)))

#print axioms Step.foldPair
#print axioms Step.destructureBind

#print axioms Step.appendKwHash

#print axioms Step.bindIvar
#print axioms Step.reifyBlock
#print axioms Step.doReturn
#print axioms Step.finishRegion

/-! ### The two folds over a bare `Machine`, and `PreAct`

`Step.foldPair` above is the fold whose accumulator is a pair; `enterUserMethod`'s phase-B
`setLocal` walk folds over the **machine alone**, so it needs the other shape.

**`PreAct` is the layer's second relation**, and it exists for one reason: the frame push at the
end of an activation reads a `MethodDef` out of the heap (`Step.push_meth`), and the machine it
pushes at is not the machine the caller read that `MethodDef` at — an activation *allocates*
first (a keyword bundle, a rest array, a kwrest hash, a destructuring bind). So the heap fact has
to travel, and `Step` alone does not carry it. `PreAct` is `Step` plus exactly that transport:
**every method installed in the heap is still installed**, which every allocation satisfies
(`methodIn_alloc`) and which is all `Sealed.meth` needs at the push.

Stated over `methodIn` — the *lookup*, not membership in `cp.methods` — for the sixth stall
point's reason, and the same one `CapAt`'s class arm was keyed that way for (clink 62): the
membership form is easier to establish and `Sealed.meth` cannot consume it.

A `frames`/`stack` conjunct was drafted alongside and **rejected as unnecessary**: the push
lemma's premises are all read at the *intermediate* machine, where `Step` already hands back
`Sealed`/`FramesWF`, so nothing has to be transported across the prefix except the heap fact. -/

theorem Step.foldM {b : FrameId} {α : Type} (f : Machine → α → Machine)
    (hf : ∀ (m : Machine) (a : α), StepInv b m → Step b m (f m a)) :
    ∀ (l : List α) (m : Machine), StepInv b m → Step b m (l.foldl f m)
  | [], m, h => Step.refl h
  | a :: rest, m, h => by
    rw [List.foldl_cons]
    exact (hf m a h).trans (Step.foldM f hf rest (f m a) (hf m a h).2)

/-- …and as a peel, for a fold reached after something else. -/
theorem Step.foldM' {b : FrameId} {α : Type} (f : Machine → α → Machine)
    (hf : ∀ (m : Machine) (a : α), StepInv b m → Step b m (f m a))
    (l : List α) {m mid : Machine} (s : Step b m mid) : Step b m (l.foldl f mid) :=
  s.trans (Step.foldM f hf l mid s.2)

/-- **`Step`, plus the two heap facts a frame push reads.** What the allocating prefix of an
activation preserves: `b`'s locals and the invariant, **every installed method is still
installed** (`enterUserMethod`'s push, via `Sealed.meth`) and **every Proc in the heap is still
there** (`callClosure`'s push, via `Sealed.clos`). Both are needed for the same reason and by
the same shape of caller — a helper that allocates before it pushes — so they travel together. -/
def PreAct (b : FrameId) (m m' : Machine) : Prop :=
  Step b m m'
  ∧ (∀ (k : ObjId) (n : String) (md : MethodDef),
      methodIn m.heap k n = some md → methodIn m'.heap k n = some md)
  ∧ (∀ (o : ObjId) (cl : Closure),
      procClosure? m.heap (.ref o) = some cl → procClosure? m'.heap (.ref o) = some cl)

theorem PreAct.refl {b : FrameId} {m : Machine} (h : StepInv b m) : PreAct b m m :=
  ⟨Step.refl h, fun _ _ _ hm => hm, fun _ _ hc => hc⟩

theorem PreAct.trans {b : FrameId} {a c d : Machine} (h₁ : PreAct b a c) (h₂ : PreAct b c d) :
    PreAct b a d :=
  ⟨h₁.1.trans h₂.1, fun k n md hm => h₂.2.1 k n md (h₁.2.1 k n md hm),
   fun o cl hc => h₂.2.2 o cl (h₁.2.2 o cl hc)⟩

theorem PreAct.allocArr {b : FrameId} {m mid : Machine} (p : PreAct b m mid) (xs : Array Value) :
    PreAct b m (Builtins.allocArr mid xs).2 :=
  ⟨Step.allocArr' p.1 xs, fun k n md hm => methodIn_alloc _ (p.2.1 k n md hm),
   fun o cl hc => procClosure_alloc _ (p.2.2 o cl hc)⟩

theorem PreAct.allocHsh {b : FrameId} {m mid : Machine} (p : PreAct b m mid)
    (xs : Array (Value × Value)) : PreAct b m (Builtins.allocHsh mid xs).2 :=
  ⟨Step.allocHsh' p.1 xs, fun k n md hm => methodIn_alloc _ (p.2.1 k n md hm),
   fun o cl hc => procClosure_alloc _ (p.2.2 o cl hc)⟩

theorem PreAct.appendKwHash {b : FrameId} {m mid : Machine} (p : PreAct b m mid)
    (args : List Value) (kw : List (Value × Value)) :
    PreAct b m (Interp.appendKwHash mid args kw).2 := by
  unfold Interp.appendKwHash
  split
  · exact p
  · exact p.allocHsh _

/-- `Step.foldPair`'s twin one relation up. -/
theorem PreAct.foldPair {b : FrameId} {α β : Type} (f : β × Machine → α → β × Machine)
    (hf : ∀ (p : β × Machine) (a : α), StepInv b p.2 → PreAct b p.2 (f p a).2) :
    ∀ (l : List α) (p : β × Machine), StepInv b p.2 → PreAct b p.2 (l.foldl f p).2
  | [], p, h => PreAct.refl h
  | a :: rest, p, h => by
    rw [List.foldl_cons]
    exact (hf p a h).trans (PreAct.foldPair f hf rest (f p a) (hf p a h).1.2)

theorem PreAct.foldPair' {b : FrameId} {α β : Type} (f : β × Machine → α → β × Machine)
    (hf : ∀ (p : β × Machine) (a : α), StepInv b p.2 → PreAct b p.2 (f p a).2)
    (l : List α) (init : β) {m mid : Machine} (s : PreAct b m mid) :
    PreAct b m (l.foldl f (init, mid)).2 :=
  s.trans (PreAct.foldPair f hf l (init, mid) s.1.2)

/-- **`destructureBind` at `PreAct`** — `Step.destructureBind`'s structure verbatim, one
relation up, because a nested `.destr` allocates a rest array at every level. -/
theorem PreAct.destructureBind {b : FrameId} :
    ∀ (fuel : Nat) (m : Machine) (subs : List RubyCore.Param) (v : Value), StepInv b m →
      PreAct b m (Interp.destructureBind m subs v fuel).2
  | 0, m, _, _, h => PreAct.refl h
  | fuel + 1, m, subs, v, h => by
    rw [Interp.destructureBind.eq_def]
    have hstep : ∀ (p : List (String × Value) × Machine) (a : RubyCore.Param × Value),
        StepInv b p.2 → PreAct b p.2 (
          (match a.1 with
            | .req nm => (p.1 ++ [(nm, a.2)], p.2)
            | .destr subs' =>
              let r := Interp.destructureBind p.2 subs' a.2 fuel
              (p.1 ++ r.1, r.2)
            | _ => (p.1, p.2)) : List (String × Value) × Machine).2 := by
      intro p a hp
      obtain ⟨pp, val⟩ := a
      cases pp
      case destr => exact PreAct.destructureBind fuel p.2 _ _ hp
      all_goals exact PreAct.refl hp
    cases v
    case ref o =>
      cases hp : (m.heap.get o).payload
      all_goals (repeat (any_goals (first
      | (refine PreAct.allocArr ?_ _; exact PreAct.foldPair _ hstep _ _ h)
      | exact PreAct.foldPair _ hstep _ _ h
      | refine PreAct.foldPair' _ hstep _ _ ?_
      | split)))
    all_goals (repeat (any_goals (first
      | (refine PreAct.allocArr ?_ _; exact PreAct.foldPair _ hstep _ _ h)
      | exact PreAct.foldPair _ hstep _ _ h
      | refine PreAct.foldPair' _ hstep _ _ ?_
      | split)))

#print axioms Step.foldM
#print axioms PreAct.destructureBind

end Ratchet.Denote