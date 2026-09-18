import Denote.Ty.Apply
import RubyCore.Proof.HeapGrow

/-!
# `Denote/Ty/Ext.lean` — allocation, and the one thing about a type's meaning that does not
survive it

`Denote/Sem/notes.md` §The fourth stall point records the wall the semantic ratchet hit at
its third literal: **a string literal allocates.** `Judge.strLit`'s post-machine is its
pre-machine with one object pushed, and re-establishing `StateOk` there means transporting
every component across the push. Eleven of the twelve components transport for a boring
reason — they read the heap through `Heap.get`/`classPayload?`, and a push moves neither.
The twelfth does not, and the reason is structural rather than fixable by a lemma: `denM`'s
**arrow** arm (and `AsmsOk`, which has the same shape) quantifies over *runs*, and a run
from the extended heap allocates at shifted object ids, so it is not the run from the
unextended one.

This file is the fix the notes said to start from the constraint of: a relation coarse
enough to seed a future-quantified arrow **without** conflicting with
`Denote/Rules/Core.lean`'s `denM_ctl`.

## `Ext` — "the same machine, later, having allocated"

`Ext m m₂` says `m₂` is `m` after some allocation and nothing else: same frames, a heap that
only grew, and — the two clauses that are not "nothing changed" — a bound on what the *fresh*
ids may be. Three properties earn it its place.

* **Reflexive and transitive**, which is what lets a future-quantified arrow be monotone:
  the arrow at `m` gives the arrow at any `m₂` with `Ext m m₂`, by composing.
* **Blind to `ctl`/`kont`**, which is what keeps `denM_ctl` true. This is exactly the
  conflict the notes flagged against a `Reaches`-indexed arrow: machines reachable from `m`
  are not machines reachable from `m` with its control word rewritten, whereas `Ext` reads
  only the heap and the frame array, both of which `reCtl` preserves.
* **Frames pinned, not merely extended.** A `clos` type's denotation reads its captured
  locals out of `Machine.frames` (`Denote/Ty/Apply.lean` §Why a `Machine`), so a relation that
  let frames grow would have to transport that too. Pinning them is the weaker, honest
  choice: the arrow this seeds is stable **under allocation**, which is strictly less than
  `Denote/Ty/Arrow.lean`'s `ArrowStable` (stable under *execution*) and is exactly what the
  allocating rungs need. Recorded as a gap, not hidden: a call rung will want the stronger
  one.

## The two fresh-id clauses, and the dangling reference they are about

`Heap.get` is total: out of bounds it answers `default`, whose `klass` is `0` — which is
`Boot.basicObjectId`. So at a heap of size `n`, the value `.ref n` is not an error, it is an
**instance of `BasicObject` with no ivars**, and after a push it becomes whatever was
pushed. Nothing in `StateOk` forbids `Γ` from typing a local that holds such a dangling
reference, so the transport has to survive it rather than assume it away.

Both clauses are about exactly that id range, and both are discharged by `rfl`-shaped facts
at a real allocation:

* `freshIvars` — a pushed literal has no instance variables, so `ivarOf` answers `nil` at a
  dangling reference **both** before and after. (`RubyCore.Proof.PlainGrow` carries the same
  clause for the same reason.)
* `freshBasic` — a pushed object is at least as much of a `BasicObject` as the dangling read
  it replaces. This is what keeps the *nominal* arm monotone: `.cls n` at a dangling
  reference can only be true for the classes in `ancestors h Boot.basicObjectId`, and a
  freshly allocated `String` has all of them.

The payload projections need no clause at all, and that is worth recording as the reason
`Ext` is this short: `default.payload` is `.none`, so `arrElems?`/`hshEntries?`/`procClosure?`
already answer `none` at every dangling reference, which makes `arrayOf`/`hashOf`/`clos`
*vacuous* there rather than in need of transport.

## What is imported, and why that is new

This is the first file in the package to import `RubyCore.Proof.*` — the model's own
metatheory, not just its interpreter. `RubyCore/Proof/AncestorsGrow.lean` solved precisely
the sub-problem in the way: `ancestors` is fuel-bounded by `h.objs.size + 1`, so a push moves
the *fuel*, and `Saturated` ("one more unit of fuel changes nothing") is the checkable
hypothesis that makes the walk agree across a growing heap. Re-deriving it here would be a
second, driftable copy of a proof that already exists against the same `stepFn`
(`Semantics/Interp.lean`'s argument for importing rather than porting, applied one layer up).
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## Out of bounds reads the default object -/

/-- `Heap.get` past the end is the default object. The single fact every dangling-reference
case below turns on. -/
theorem get_oob (h : Heap) {o : ObjId} (ho : h.objs.size ≤ o) : h.get o = default := by
  simp only [Heap.get, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_none (by omega), Option.getD_none]

theorem classOf_oob (h : Heap) {o : ObjId} (ho : h.objs.size ≤ o) :
    classOf h (.ref o) = Boot.basicObjectId := by
  simp only [classOf, get_oob h ho]; rfl

/-- Every payload projection is `none` at a dangling reference: `default.payload` is
`.none`. This is why `Ext` needs no clause about array, hash or proc payloads. -/
theorem arrElems?_oob (h : Heap) {o : ObjId} (ho : h.objs.size ≤ o) :
    arrElems? h (.ref o) = none := by
  simp only [arrElems?, get_oob h ho]; rfl

theorem hshEntries?_oob (h : Heap) {o : ObjId} (ho : h.objs.size ≤ o) :
    hshEntries? h (.ref o) = none := by
  simp only [hshEntries?, get_oob h ho]; rfl

theorem procClosure?_oob (h : Heap) {o : ObjId} (ho : h.objs.size ≤ o) :
    procClosure? h (.ref o) = none := by
  simp only [procClosure?, get_oob h ho]; rfl

theorem ivarOf_oob (h : Heap) {o : ObjId} (ho : h.objs.size ≤ o) (x : String) :
    ivarOf h (.ref o) x = .nil := by
  simp only [ivarOf, get_oob h ho]; rfl

/-- A payload projection that *succeeds* pins its reference in range — the converse the
transport actually uses, since it arrives holding `arrElems? h v = some xs` rather than a
bound on `v`. -/
theorem lt_of_arrElems? {h : Heap} {o : ObjId} {xs : Array Value}
    (hx : arrElems? h (.ref o) = some xs) : o < h.objs.size := by
  rcases Nat.lt_or_ge o h.objs.size with hc | hc
  · exact hc
  · rw [arrElems?_oob h hc] at hx; exact absurd hx (by simp)

theorem lt_of_hshEntries? {h : Heap} {o : ObjId} {es : Array (Value × Value)}
    (hx : hshEntries? h (.ref o) = some es) : o < h.objs.size := by
  rcases Nat.lt_or_ge o h.objs.size with hc | hc
  · exact hc
  · rw [hshEntries?_oob h hc] at hx; exact absurd hx (by simp)

theorem lt_of_procClosure? {h : Heap} {o : ObjId} {cl : Closure}
    (hx : procClosure? h (.ref o) = some cl) : o < h.objs.size := by
  rcases Nat.lt_or_ge o h.objs.size with hc | hc
  · exact hc
  · rw [procClosure?_oob h hc] at hx; exact absurd hx (by simp)

/-! ## The relation -/

/-- **`m₂` is `m` after an allocation.** See the module docstring for each clause. -/
structure Ext (m m₂ : Machine) : Prop where
  /-- The frame array is untouched: a `clos`'s captured scope still resolves. -/
  frames : m₂.frames = m.frames
  /-- And so is the frame *stack*, which `Machine.getLocal` starts its walk from. -/
  stack : m₂.stack = m.stack
  /-- The heap only grows. -/
  size : m.heap.objs.size ≤ m₂.heap.objs.size
  /-- Every id the old heap had reads back identically. -/
  get : ∀ o, o < m.heap.objs.size → m₂.heap.get o = m.heap.get o
  /-- Nothing anywhere became — or stopped being — a class. -/
  payload : ∀ k, m₂.heap.classPayload? k = m.heap.classPayload? k
  /-- **The ancestor walk is unmoved**, which the four clauses above do *not* give:
      `ancestors` is fuel-bounded by `h.objs.size + 1` (`RubyCore/Heap.lean`, L73 — a
      `partial def` would be opaque to the kernel), so growing the heap grows the fuel.
      `RubyCore.Proof.ancestors_congr_grow` discharges this from the clauses above plus
      `Saturated`, and every producer of an `Ext` below cites it; it is a *clause* rather
      than a consequence because carrying `Saturated` inside `Ext` would make `Ext.refl`
      conditional, and a reflexivity that can fail is not one. -/
  ancestors : ∀ k, RubyCore.ancestors m₂.heap k = RubyCore.ancestors m.heap k
  /-- A fresh object has no instance variables, so `ivarOf` still answers `nil` there. -/
  freshIvars : ∀ o, m.heap.objs.size ≤ o → (m₂.heap.get o).ivars = []
  /-- A fresh object is at least as much of a `BasicObject` as the dangling read it
      replaces. -/
  freshBasic : ∀ o, m.heap.objs.size ≤ o → ∀ k,
    (RubyCore.ancestors m.heap Boot.basicObjectId).contains k = true →
    (RubyCore.ancestors m₂.heap (classOf m₂.heap (.ref o))).contains k = true
  /-- Allocation preserves bounded class/dispatch edges. Old-object agreement alone
      says nothing about the `klass` or `eigen` pointers of a fresh object. -/
  chains : Proof.ChainsIn m.heap → Proof.ChainsIn m₂.heap

/-! ## `Later` — the arrow's quantifier

`Ext` pins the frame array, which is what makes it useless as the domain of the arrow arm the
moment a rule **rebinds a local**: `Judge.vasgn`'s post-machine has a mutated frame, so an
arrow (or an `AsmsOk` row) stated over `Ext`-futures of the pre-machine says nothing at the
post-machine. `Later` is the coarser relation those two quantify over instead: the heap only
grew, the frame *stack* and the frame *count* are where they were, and the frames' contents
may have been rebound.

Two relations rather than one, and the split is forced:

* the **arrow** and **`AsmsOk`** quantify over runs, so they need the *widest* domain that is
  still monotone — every machine change a rule can make has to land inside it, or the claim
  does not survive the rule;
* `denM`'s **`clos`** arm reads `Machine.frames` directly (`closLocal`), so it is *not*
  monotone under a rebinding, and it must not be: that is exactly the fact
  `found-issues.md` §F1 turned on. Its transport is `Ext` (allocation, frames pinned) plus
  `capStale` (rebinding, `Denote/Ty/Local.lean`), never a quantifier.

`Later` is deliberately permissive about *what* the frames now hold, because nothing in this
package has to **establish** an arrow — no `Judge` rule concludes one, and `Denote/Ty/Arrow.lean`
keeps `ArrowFlat` as the shape a single call is stated against. Each rung that needs the arrow
to survive one more kind of machine change widens this relation by one clause, and the
destination is written down: `ArrowStable`, the arrow at every *reachable* machine
(`Denote/Ty/Arrow.lean`), which is what a call-it-later arrow honestly means. `Later` is that
target approximated from below, by the step kinds the ladder has actually met. -/
structure Later (m m₂ : Machine) : Prop where
  /-- The frame stack is where it was: the *current* frame is still the current frame. -/
  stack : m₂.stack = m.stack
  /-- No frame was pushed or popped. Their contents may have been rebound. -/
  frameCount : m₂.frames.size = m.frames.size
  size : m.heap.objs.size ≤ m₂.heap.objs.size
  /-- **The heap's *shape* is where it was**, object by object — but not its contents.
      `Ext.get` says the whole object reads back identically; this says only that its class,
      eigenclass, payload and frozen bit do, which is the widening `Judge.ivarAsgn` needed
      (an instance-variable write mutates an existing object, so it is not an `Ext`, and this
      structure's docstring says each rung that meets a new kind of machine change widens the
      relation by one clause). Nothing consumes more than this: the arrow's own content reads
      `isProcV` — a payload test — and quantifies the rest over runs. -/
  klass : ∀ o, o < m.heap.objs.size → (m₂.heap.get o).klass = (m.heap.get o).klass
  eigen : ∀ o, o < m.heap.objs.size → (m₂.heap.get o).eigen = (m.heap.get o).eigen
  payloadObj : ∀ o, o < m.heap.objs.size → (m₂.heap.get o).payload = (m.heap.get o).payload
  frozen : ∀ o, o < m.heap.objs.size → (m₂.heap.get o).frozen = (m.heap.get o).frozen
  payload : ∀ k, m₂.heap.classPayload? k = m.heap.classPayload? k
  ancestors : ∀ k, RubyCore.ancestors m₂.heap k = RubyCore.ancestors m.heap k

theorem Later.refl (m : Machine) : Later m m where
  stack := rfl
  frameCount := rfl
  size := Nat.le_refl _
  klass := fun _ _ => rfl
  eigen := fun _ _ => rfl
  payloadObj := fun _ _ => rfl
  frozen := fun _ _ => rfl
  payload := fun _ => rfl
  ancestors := fun _ => rfl

theorem Later.trans {m m₂ m₃ : Machine} (h₁ : Later m m₂) (h₂ : Later m₂ m₃) : Later m m₃ where
  stack := by rw [h₂.stack, h₁.stack]
  frameCount := by rw [h₂.frameCount, h₁.frameCount]
  size := Nat.le_trans h₁.size h₂.size
  klass := fun o ho => by
    rw [h₂.klass o (Nat.lt_of_lt_of_le ho h₁.size), h₁.klass o ho]
  eigen := fun o ho => by
    rw [h₂.eigen o (Nat.lt_of_lt_of_le ho h₁.size), h₁.eigen o ho]
  payloadObj := fun o ho => by
    rw [h₂.payloadObj o (Nat.lt_of_lt_of_le ho h₁.size), h₁.payloadObj o ho]
  frozen := fun o ho => by
    rw [h₂.frozen o (Nat.lt_of_lt_of_le ho h₁.size), h₁.frozen o ho]
  payload := fun k => by rw [h₂.payload k, h₁.payload k]
  ancestors := fun k => by rw [h₂.ancestors k, h₁.ancestors k]

/-- Every allocation is a `Later`. This is what lets `denM_ext` transport the arrow arm with
no work at all: `Ext.trans` on the outside became `Later.trans` on the inside. -/
theorem Ext.later {m m₂ : Machine} (he : Ext m m₂) : Later m m₂ where
  stack := he.stack
  frameCount := by rw [he.frames]
  size := he.size
  klass := fun o ho => by rw [he.get o ho]
  eigen := fun o ho => by rw [he.get o ho]
  payloadObj := fun o ho => by rw [he.get o ho]
  frozen := fun o ho => by rw [he.get o ho]
  payload := he.payload
  ancestors := he.ancestors

/-- A Proc stays a Proc across a `Later`, for `Ext.isProcV_mono`'s reason: a payload
projection that *succeeded* read an object the old heap already had. -/
theorem Later.procClosure?_eq {m m₂ : Machine} (he : Later m m₂) {v : Value} {cl : Closure}
    (h : procClosure? m.heap v = some cl) : procClosure? m₂.heap v = some cl := by
  cases v with
  | ref o =>
    rw [procClosure?, he.payloadObj o (lt_of_procClosure? h)]
    exact h
  | _ => exact absurd h (by simp [procClosure?])

theorem Later.isProcV_mono {m m₂ : Machine} (he : Later m m₂) {v : Value}
    (h : isProcV m.heap v = true) : isProcV m₂.heap v = true := by
  simp only [isProcV, Option.isSome_iff_exists] at *
  obtain ⟨cl, hcl⟩ := h
  exact ⟨cl, he.procClosure?_eq hcl⟩

theorem Ext.shapeAgree {m m₂ : Machine} (he : Ext m m₂) :
    Proof.ShapeAgree m.heap m₂.heap := fun k => by rw [he.payload k]

theorem Ext.refl (m : Machine) : Ext m m where
  frames := rfl
  stack := rfl
  size := Nat.le_refl _
  get := fun _ _ => rfl
  payload := fun _ => rfl
  ancestors := fun _ => rfl
  freshIvars := fun o ho => by rw [get_oob m.heap ho]; rfl
  freshBasic := fun o ho k hk => by rw [classOf_oob m.heap ho]; exact hk
  chains := id

theorem Ext.trans {m m₂ m₃ : Machine} (h₁ : Ext m m₂) (h₂ : Ext m₂ m₃) : Ext m m₃ where
  frames := by rw [h₂.frames, h₁.frames]
  stack := by rw [h₂.stack, h₁.stack]
  size := Nat.le_trans h₁.size h₂.size
  get := fun o ho => by rw [h₂.get o (Nat.lt_of_lt_of_le ho h₁.size), h₁.get o ho]
  payload := fun k => by rw [h₂.payload k, h₁.payload k]
  ancestors := fun k => by rw [h₂.ancestors k, h₁.ancestors k]
  chains := h₂.chains ∘ h₁.chains
  freshIvars := fun o ho => by
    by_cases hc : o < m₂.heap.objs.size
    · rw [h₂.get o hc]; exact h₁.freshIvars o ho
    · exact h₂.freshIvars o (Nat.le_of_not_lt hc)
  freshBasic := fun o ho k hk => by
    by_cases hc : o < m₂.heap.objs.size
    · have hclass : classOf m₃.heap (.ref o) = classOf m₂.heap (.ref o) := by
        simp only [classOf, h₂.get o hc]
      rw [hclass, h₂.ancestors]
      exact h₁.freshBasic o ho k hk
    · exact h₂.freshBasic o (Nat.le_of_not_lt hc) k (by rw [h₁.ancestors]; exact hk)

/-! ## What the probes do across an `Ext`

One lemma per probe in `Denote/Ty/Val.lean`, and the split between the ones that are *equal*
and the one that is only *monotone* is the whole content of the section: everything that
reads a class payload or an object in range agrees exactly, and `isA` — the one probe that
can see a dangling reference turn into a real object — only goes one way. -/

theorem Ext.constLookup_eq {m m₂ : Machine} (he : Ext m m₂) (n : String) :
    constLookup m₂.heap n = constLookup m.heap n := by
  simp only [constLookup, he.payload]

theorem Ext.classNamed?_eq {m m₂ : Machine} (he : Ext m m₂) (n : String) :
    classNamed? m₂.heap n = classNamed? m.heap n := by
  simp only [classNamed?, he.constLookup_eq]
  cases constLookup m.heap n with
  | none => rfl
  | some v => cases v <;> simp [he.payload]

theorem Ext.isClassRefNamed_eq {m m₂ : Machine} (he : Ext m m₂) (v : Value) (n : String) :
    isClassRefNamed m₂.heap v n = isClassRefNamed m.heap v n := by
  simp only [isClassRefNamed, he.classNamed?_eq]

/-- **The one-way probe.** A value that is an `n` stays an `n`; the converse fails at exactly
one place, which is why `Ext` exists at all — a dangling `.ref` reads as a bare
`BasicObject` before the push and as the pushed object after it. -/
theorem Ext.isA_mono {m m₂ : Machine} (he : Ext m m₂) {v : Value} {k : ObjId}
    (h : isA m.heap v k = true) : isA m₂.heap v k = true := by
  cases v with
  | ref o =>
    rcases Nat.lt_or_ge o m.heap.objs.size with hc | hc
    · have : classOf m₂.heap (.ref o) = classOf m.heap (.ref o) := by
        simp only [classOf, he.get o hc]
      simpa only [isA, this, he.ancestors] using h
    · refine he.freshBasic o hc k ?_
      rwa [isA, classOf_oob m.heap hc] at h
  | int _ | flt _ | sym _ | nil => simpa only [isA, classOf, he.ancestors] using h
  | bool b => cases b <;> simpa only [isA, classOf, he.ancestors] using h

/-- **The exact-instance reading is `Ext`-monotone too**, and this is where the liveness
conjunct in `isExactInst` earns its place: an `Ext` pins `classNamed?` and pins `Heap.get` at
every id the old heap had, so an object that was exactly an `n` still is. Without the range
test the lemma is false — a *dangling* reference reads as `default` (class `0`) before the
allocation and as a real object after it. -/
theorem Ext.isExactInst_mono {m m₂ : Machine} (he : Ext m m₂) {v : Value} {n : String}
    (h : isExactInst m.heap v n = true) : isExactInst m₂.heap v n = true := by
  unfold isExactInst at h ⊢
  rw [he.classNamed?_eq] at *
  cases hcn : classNamed? m.heap n with
  | none => rw [hcn] at h; cases v <;> simp_all
  | some k =>
    rw [hcn] at h
    cases v with
    | ref o =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢
      obtain ⟨⟨hlt, heig⟩, hco⟩ := h
      exact ⟨⟨Nat.lt_of_lt_of_le hlt he.size, by rw [he.get o hlt]; exact heig⟩,
        by rw [he.get o hlt]; exact hco⟩
    | _ => simp_all

theorem Ext.isAName_mono {m m₂ : Machine} (he : Ext m m₂) {v : Value} {n : String}
    (h : isAName m.heap v n = true) : isAName m₂.heap v n = true := by
  unfold isAName at h ⊢
  rw [he.classNamed?_eq]
  cases hk : classNamed? m.heap n with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k => rw [hk] at h; exact he.isA_mono h

/-- The payload projections, at a reference the *old* heap already resolved. Stated with the
success as the hypothesis, because that is the form the transport arrives in. -/
theorem Ext.arrElems?_eq {m m₂ : Machine} (he : Ext m m₂) {v : Value} {xs : Array Value}
    (h : arrElems? m.heap v = some xs) : arrElems? m₂.heap v = some xs := by
  cases v with
  | ref o => rw [arrElems?, he.get o (lt_of_arrElems? h)]; exact h
  | _ => exact absurd h (by simp [arrElems?])

theorem Ext.hshEntries?_eq {m m₂ : Machine} (he : Ext m m₂) {v : Value}
    {es : Array (Value × Value)} (h : hshEntries? m.heap v = some es) :
    hshEntries? m₂.heap v = some es := by
  cases v with
  | ref o => rw [hshEntries?, he.get o (lt_of_hshEntries? h)]; exact h
  | _ => exact absurd h (by simp [hshEntries?])

theorem Ext.procClosure?_eq {m m₂ : Machine} (he : Ext m m₂) {v : Value} {cl : Closure}
    (h : procClosure? m.heap v = some cl) : procClosure? m₂.heap v = some cl := by
  cases v with
  | ref o => rw [procClosure?, he.get o (lt_of_procClosure? h)]; exact h
  | _ => exact absurd h (by simp [procClosure?])

theorem Ext.isProcV_mono {m m₂ : Machine} (he : Ext m m₂) {v : Value}
    (h : isProcV m.heap v = true) : isProcV m₂.heap v = true := by
  simp only [isProcV, Option.isSome_iff_exists] at *
  obtain ⟨cl, hcl⟩ := h
  exact ⟨cl, he.procClosure?_eq hcl⟩

/-- **`ivarOf` agrees everywhere**, including at a dangling reference: `default` has no
ivars and `freshIvars` says the object that replaces it has none either, so both answer
`nil`. This is what makes the `inst` arm's spine transport without a side condition. -/
theorem Ext.ivarOf_eq {m m₂ : Machine} (he : Ext m m₂) (v : Value) (x : String) :
    ivarOf m₂.heap v x = ivarOf m.heap v x := by
  cases v with
  | ref o =>
    rcases Nat.lt_or_ge o m.heap.objs.size with hc | hc
    · simp only [ivarOf, he.get o hc]
    · simp only [ivarOf, get_oob m.heap hc, he.freshIvars o hc]; rfl
  | _ => rfl

/-! ## The frame-indexed readers

`Ext` pins the frame array outright, so every one of these is a rewrite. -/

theorem Ext.getLocal_go_eq {m m₂ : Machine} (he : Ext m m₂) (x : String) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.getLocal.go m₂ x fid fuel = Machine.getLocal.go m x fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [Machine.getLocal.go, he.frames]
    split
    · rfl
    · split
      · exact ih _
      · rfl

@[simp] theorem Ext.getLocal_eq {m m₂ : Machine} (he : Ext m m₂) (x : String) :
    m₂.getLocal x = m.getLocal x := by
  simp only [Machine.getLocal, he.stack, he.frames]
  exact he.getLocal_go_eq x _ _

theorem Ext.frameLocal_go_eq {m m₂ : Machine} (he : Ext m m₂) (x : String) :
    ∀ (fuel : Nat) (fid : FrameId),
      frameLocal.go m₂ x fid fuel = frameLocal.go m x fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [frameLocal.go, he.frames]
    split
    · rfl
    · split
      · exact ih _
      · rfl

@[simp] theorem Ext.frameLocal_eq {m m₂ : Machine} (he : Ext m m₂) (fid : FrameId)
    (x : String) : frameLocal m₂ fid x = frameLocal m fid x := by
  simp only [frameLocal, he.frames]
  exact he.frameLocal_go_eq x _ _

@[simp] theorem Ext.frameLocal?_eq {m m₂ : Machine} (he : Ext m m₂) (fid? : Option FrameId)
    (x : String) : frameLocal? m₂ fid? x = frameLocal? m fid? x := by
  cases fid? with
  | none => rfl
  | some fid => exact he.frameLocal_eq fid x

@[simp] theorem Ext.closLocal_eq {m m₂ : Machine} (he : Ext m m₂) (cl : Closure) :
    closLocal m₂ cl = closLocal m cl := by
  funext x; exact he.frameLocal?_eq cl.captured x

@[simp] theorem Ext.closSelf_eq {m m₂ : Machine} (he : Ext m m₂) (cl : Closure) :
    closSelf m₂ cl = closSelf m cl := by
  simp only [closSelf, he.frames]

@[simp] theorem Ext.currentFrame_eq {m m₂ : Machine} (he : Ext m m₂) :
    m₂.currentFrame = m.currentFrame := by
  simp only [Machine.currentFrame, he.frames, he.stack]

#print axioms Ext.isA_mono
#print axioms Ext.ivarOf_eq

end Ratchet.Denote
