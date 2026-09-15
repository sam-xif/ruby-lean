import RubyCore.Proof.HeapFacts
import RubyCore.HeapCert

/-!
# The ancestor walk across a **growing** heap (L144, producer's bill item 3)

`Proof/HeapFacts.lean`'s congruence chain — `modAncestors_congr`, `ancestors_congr`
— requires `h'.objs.size = h.objs.size`, and uses that hypothesis **twice, both
times as a fuel rewrite and nothing else**: `ancestors` and `modAncestors` are
fuel-bounded rather than `partial` (L73, so that dispatch stays kernel-reducible),
and the fuel they take is `h.objs.size + 1`. An allocating step therefore has no
ancestor congruence at all, which is the blocker three consecutive sessions named
as the one thing between here and a producer for the class type.

This file removes it, and the interesting part is **which** heap clause does the
job.

## The route `HANDOFF.md` proposed does not exist

The proposal was: *the superclass chain descends in `ObjId`* — a subclass is
allocated after its superclass — so the walk from `k` takes at most `k + 1` steps,
any fuel `≥ k + 1` computes the same list, and F0's `heapOkB` certificate can
absorb the clause because it is decidable at the boot heap.

It is decidable, and it is **false**. `scripts/probes/ancestors_probe.lean` measures it at
the prelude-booted heap and reports **ten** non-descending edges, starting with the
ones the object model cannot do without:

```
include: Object (1) → Kernel (33)
superclass: Integer (7) → Numeric (34)
include: String (9) → Comparable (40)
include: Array (11) → Enumerable (42)
```

The reason is structural rather than accidental: the boot heap's ids are **fixed
constants** (`Boot.objectId = 1`, `Boot.integerId = 7`), while `Kernel`, `Numeric`,
`Comparable` and `Enumerable` are *prelude* Ruby and are allocated afterwards. So
the classes with the smallest ids are exactly the ones pointing at the largest, and
no re-ordering of the prelude fixes it while the boot ids are literals. The walk is
also not only the superclass chain — `ancestors` splices `includes` and `prepends`
and `modAncestors` recurses through modules — which is what makes the mixin edges
count.

## What is true, and it is what the fuel actually needs

The fuel does not care that the walk is short. It cares that the walk has
**finished** before the fuel runs out, and that is a different, weaker, *directly
checkable* property:

    the walk is stable at the fuel the heap hands it

i.e. one more unit of fuel changes nothing. Measured at the booted heap: **zero**
classes whose walk changes when the heap grows by one, and zero that need even the
last unit of the fuel they get. `Saturated` below is that property, `saturatedB` is
it as a `Bool`, and `saturatedB_sound` is the reflection — the same shape as F0's
certificate (L135) and the same trade D1 makes for `bound_suffices`: a hypothesis
the harness can check beats an `axiom`, and beats a proof nobody has finished.

Saturation is **not** derivable from the shape agreement it sits beside: a heap with
a cyclic `include` (nothing in the `Heap` type forbids one) consumes all its fuel,
and then different fuels genuinely give different answers. It is a real clause, and
it is stated as one.

## What this does *not* cover, and the measurement that says the rest is true

`ancestors_congr_grow` takes `ShapeAgree h h'` **unrelativized** — at every id,
including the ids `h` did not have. That is satisfied by allocating a *plain
object*, which is what the producer for `.cls C` values does: a non-class has
`classPayload? = none` in both heaps, so the shapes agree at the fresh id too.

It is **not** satisfied by allocating a *class* (`classDef`), where the fresh id has
a shape in `h'` and none in `h`. Typing `class C … end` therefore owes one more
clause — *no in-bounds object has an edge pointing out of bounds*, which makes the
walk from an old id stay among old ids and lets the shape agreement be relativized
the way `TypeAgree` now is (L143). `scripts/probes/ancestors_probe.lean` measures that
clause too, and it holds (0 out-of-bounds edges), so this is a proof that is owed
rather than a fact in doubt.
-/

namespace RubyCore
namespace Proof

/-! ## 0. `ChainsIn` (J43 / W2a) — no in-bounds object has a chain edge pointing
out of bounds

The clause this file's header names as *owed* by a class-allocating step, now a
carried invariant: `ancestors`/`classOf`/`lookup` from an old id must never reach
a fresh id, and these are the fields those walks read. The `boot` clause carries
the handful of literal class ids the fragment's producers allocate at, so the
transport at each `alloc` site has its bound in hand. Decided by `chainsInB` at a
concrete heap (the probe's "0 out-of-bounds edges", now kernel-checked). -/

structure ChainsIn (h : Heap) : Prop where
  boot : Boot.classId < h.objs.size ∧ Boot.moduleId < h.objs.size ∧
         Boot.hashId < h.objs.size ∧ Boot.procId < h.objs.size ∧
         Boot.objectId < h.objs.size
  klass : ∀ o, o < h.objs.size → (h.get o).klass < h.objs.size
  eigen : ∀ o, o < h.objs.size → ∀ e, (h.get o).eigen = some e → e < h.objs.size
  chain : ∀ o cp, o < h.objs.size → h.classPayload? o = some cp →
    (∀ s, cp.superclass = some s → s < h.objs.size) ∧
    (∀ i ∈ cp.includes, i < h.objs.size) ∧
    (∀ q ∈ cp.prepends, q < h.objs.size)

def chainsInB (h : Heap) : Bool :=
  decide (Boot.classId < h.objs.size) && decide (Boot.moduleId < h.objs.size) &&
  decide (Boot.hashId < h.objs.size) && decide (Boot.procId < h.objs.size) &&
  decide (Boot.objectId < h.objs.size) &&
  (List.range h.objs.size).all fun o =>
    decide ((h.get o).klass < h.objs.size) &&
    (match (h.get o).eigen with
     | some e => decide (e < h.objs.size)
     | none => true) &&
    (match h.classPayload? o with
     | some cp =>
       (match cp.superclass with
        | some s => decide (s < h.objs.size)
        | none => true) &&
       cp.includes.all (fun i => decide (i < h.objs.size)) &&
       cp.prepends.all (fun q => decide (q < h.objs.size))
     | none => true)

theorem chainsInB_sound {h : Heap} (hb : chainsInB h = true) : ChainsIn h := by
  unfold chainsInB at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨hc, hm⟩, hh⟩, hp⟩, ho⟩, hall⟩ := hb
  refine ⟨⟨hc, hm, hh, hp, ho⟩, fun o hlt => ?_, fun o hlt e he => ?_,
    fun o cp hlt hcp => ?_⟩
  · exact (hall o (List.mem_range.mpr hlt)).1.1
  · have h2 := (hall o (List.mem_range.mpr hlt)).1.2
    rw [he] at h2
    simpa using h2
  · have h3 := (hall o (List.mem_range.mpr hlt)).2
    rw [hcp] at h3
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h3
    refine ⟨fun s hs => ?_, fun i hi => ?_, fun q hq => ?_⟩
    · have := h3.1.1; rw [hs] at this; simpa using this
    · have := h3.1.2 i hi; simpa using this
    · have := h3.2 q hq; simpa using this

/-- Across a push of an object whose own fields are bounded. -/
theorem chainsIn_push {h : Heap} {obj : Object}
    (hch : ChainsIn h)
    (hkl : obj.klass < h.objs.size)
    (heig : obj.eigen = none)
    (hcp : ∀ cp, obj.payload = .cls cp →
      (∀ s, cp.superclass = some s → s < h.objs.size) ∧
      (∀ i ∈ cp.includes, i < h.objs.size) ∧
      (∀ q ∈ cp.prepends, q < h.objs.size)) :
    ChainsIn ⟨h.objs.push obj⟩ := by
  have hsz : (Heap.mk (h.objs.push obj)).objs.size = h.objs.size + 1 := by simp
  have hgold : ∀ o, o < h.objs.size → (Heap.get ⟨h.objs.push obj⟩ o) = h.get o := by
    intro o ho
    simp only [Heap.get, Array.getD_eq_getD_getElem?, Array.getElem?_push,
      if_neg (Nat.ne_of_lt ho)]
  have hgnew : (Heap.get ⟨h.objs.push obj⟩ h.objs.size) = obj := by
    simp [Heap.get, Array.getD_eq_getD_getElem?]
  have hsplit : ∀ o, o < h.objs.size + 1 → o < h.objs.size ∨ o = h.objs.size :=
    fun o hlt => Nat.lt_succ_iff_lt_or_eq.mp hlt
  obtain ⟨b1, b2, b3, b4, b5⟩ := hch.boot
  refine ⟨⟨by rw [hsz]; exact Nat.lt_succ_of_lt b1,
      by rw [hsz]; exact Nat.lt_succ_of_lt b2,
      by rw [hsz]; exact Nat.lt_succ_of_lt b3,
      by rw [hsz]; exact Nat.lt_succ_of_lt b4,
      by rw [hsz]; exact Nat.lt_succ_of_lt b5⟩,
    fun o hlt => ?_, fun o hlt e he => ?_, fun o cp hlt hcp2 => ?_⟩
  · rw [hsz] at hlt ⊢
    rcases hsplit o hlt with hlo | rfl
    · rw [hgold o hlo]; exact Nat.lt_succ_of_lt (hch.klass o hlo)
    · rw [hgnew]; exact Nat.lt_succ_of_lt hkl
  · rw [hsz] at hlt ⊢
    rcases hsplit o hlt with hlo | rfl
    · rw [hgold o hlo] at he
      exact Nat.lt_succ_of_lt (hch.eigen o hlo e he)
    · rw [hgnew] at he; rw [heig] at he; exact absurd he (by simp)
  · rw [hsz] at hlt
    rcases hsplit o hlt with hlo | rfl
    · have hcp3 : h.classPayload? o = some cp := by
        unfold Heap.classPayload? at hcp2 ⊢
        rw [hgold o hlo] at hcp2
        exact hcp2
      obtain ⟨h1, h2, h3⟩ := hch.chain o cp hlo hcp3
      refine ⟨fun sc hs => ?_, fun i hi => ?_, fun q hq => ?_⟩
      · rw [hsz]; exact Nat.lt_succ_of_lt (h1 sc hs)
      · rw [hsz]; exact Nat.lt_succ_of_lt (h2 i hi)
      · rw [hsz]; exact Nat.lt_succ_of_lt (h3 q hq)
    · unfold Heap.classPayload? at hcp2
      rw [hgnew] at hcp2
      cases hpl : obj.payload with
      | cls c =>
        rw [hpl] at hcp2
        simp only [Option.some.injEq] at hcp2
        subst hcp2
        obtain ⟨h1, h2, h3⟩ := hcp c hpl
        refine ⟨fun sc hs => ?_, fun i hi => ?_, fun q hq => ?_⟩
        · rw [hsz]; exact Nat.lt_succ_of_lt (h1 sc hs)
        · rw [hsz]; exact Nat.lt_succ_of_lt (h2 i hi)
        · rw [hsz]; exact Nat.lt_succ_of_lt (h3 q hq)
      | _ => rw [hpl] at hcp2; exact absurd hcp2 (by simp)

/-- The plain-push instance: a non-class object with no eigenclass. -/
theorem chainsIn_alloc {h : Heap} {obj : Object}
    (hch : ChainsIn h) (hkl : obj.klass < h.objs.size) (heig : obj.eigen = none)
    (hnc : ∀ c, obj.payload ≠ .cls c) :
    ChainsIn ⟨h.objs.push obj⟩ :=
  chainsIn_push hch hkl heig (fun cp hcp => absurd hcp (hnc cp))

theorem get_defineMethod_eigen (h : Heap) (cls : ObjId) (name : String)
    (md : MethodDef) (o : ObjId) :
    ((defineMethod h cls name md).get o).eigen = (h.get o).eigen := by
  unfold defineMethod
  cases hc : h.classPayload? cls with
  | none => rfl
  | some c =>
    by_cases ho : o = cls
    · subst ho
      by_cases hb : o < h.objs.size
      · simp only [Heap.setClassPayload, Heap.get, Heap.set]
        rw [objs_getD_set!_self _ _ _ hb]
      · simp only [Heap.setClassPayload, Heap.get, Heap.set]
        rw [objs_getD_set!_oob _ _ _ hb]
    · simp only [Heap.setClassPayload, Heap.get, Heap.set]
      rw [objs_getD_set!_ne _ _ _ _ ho]

theorem get_defineMethod_klass (h : Heap) (cls : ObjId) (name : String)
    (md : MethodDef) (o : ObjId) :
    ((defineMethod h cls name md).get o).klass = (h.get o).klass := by
  unfold defineMethod
  cases hc : h.classPayload? cls with
  | none => rfl
  | some c =>
    by_cases ho : o = cls
    · subst ho
      by_cases hb : o < h.objs.size
      · simp only [Heap.setClassPayload, Heap.get, Heap.set]
        rw [objs_getD_set!_self _ _ _ hb]
      · simp only [Heap.setClassPayload, Heap.get, Heap.set]
        rw [objs_getD_set!_oob _ _ _ hb]
    · simp only [Heap.setClassPayload, Heap.get, Heap.set]
      rw [objs_getD_set!_ne _ _ _ _ ho]

/-- Chain-edge equality out of a `clsShape` agreement, at one id. -/
theorem chainEdges_of_shape {h h' : Heap} {o : ObjId} {cp cp' : ClassPayload}
    (hsh : (h'.classPayload? o).map clsShape = (h.classPayload? o).map clsShape)
    (hcp' : h'.classPayload? o = some cp') (hcp : h.classPayload? o = some cp) :
    cp'.superclass = cp.superclass ∧ cp'.includes = cp.includes ∧
      cp'.prepends = cp.prepends := by
  rw [hcp', hcp] at hsh
  simp only [Option.map_some, Option.some.injEq, clsShape, Prod.mk.injEq] at hsh
  exact ⟨hsh.2.2, hsh.2.1, hsh.1⟩

theorem chainsIn_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hch : ChainsIn h) : ChainsIn (defineMethod h cls name md) := by
  have hsz := objs_size_defineMethod h cls name md
  refine ⟨by rw [hsz]; exact hch.boot, fun o hlt => ?_, fun o hlt e he => ?_,
    fun o cp hlt hcp => ?_⟩
  · rw [hsz] at hlt ⊢
    rw [get_defineMethod_klass]
    exact hch.klass o hlt
  · rw [hsz] at hlt ⊢
    rw [get_defineMethod_eigen] at he
    exact hch.eigen o hlt e he
  · rw [hsz] at hlt
    have hsh := shape_defineMethod h cls o name md
    have hs0 : (h.classPayload? o).isSome := by
      have := classPayload?_isSome_defineMethod h cls o name md
      rw [hcp] at this
      exact this.symm ▸ (by simp)
    cases hcp0 : h.classPayload? o with
    | none => rw [hcp0] at hs0; exact absurd hs0 (by simp)
    | some cp0 =>
      obtain ⟨hsup, hinc, hpre⟩ := chainEdges_of_shape hsh hcp hcp0
      obtain ⟨h1, h2, h3⟩ := hch.chain o cp0 hlt hcp0
      rw [hsup, hinc, hpre]
      exact ⟨fun sc hs => by rw [hsz]; exact h1 sc hs,
        fun i hi => by rw [hsz]; exact h2 i hi,
        fun q hq => by rw [hsz]; exact h3 q hq⟩

theorem chainsIn_constSetIn {h : Heap} {j : ObjId} {nm : String} {v : Value}
    (hch : ChainsIn h) : ChainsIn (constSetIn h j nm v) := by
  have hsz := objs_size_constSetIn h j nm v
  refine ⟨by rw [hsz]; exact hch.boot, fun o hlt => ?_, fun o hlt e he => ?_,
    fun o cp hlt hcp => ?_⟩
  · rw [hsz] at hlt ⊢
    rw [(get_constSetIn_fields h j nm v o).2.1]
    exact hch.klass o hlt
  · rw [hsz] at hlt ⊢
    rw [(get_constSetIn_fields h j nm v o).2.2.1] at he
    exact hch.eigen o hlt e he
  · rw [hsz] at hlt
    have hsh := shape_constSetIn h j o nm v
    have hs0 : (h.classPayload? o).isSome := by
      have := classPayload?_isSome_constSetIn h j o nm v
      rw [hcp] at this
      exact this.symm ▸ (by simp)
    cases hcp0 : h.classPayload? o with
    | none => rw [hcp0] at hs0; exact absurd hs0 (by simp)
    | some cp0 =>
      obtain ⟨hsup, hinc, hpre⟩ := chainEdges_of_shape hsh hcp hcp0
      obtain ⟨h1, h2, h3⟩ := hch.chain o cp0 hlt hcp0
      rw [hsup, hinc, hpre]
      exact ⟨fun sc hs => by rw [hsz]; exact h1 sc hs,
        fun i hi => by rw [hsz]; exact h2 i hi,
        fun q hq => by rw [hsz]; exact h3 q hq⟩

theorem chainsIn_ivarOnly {h h' : Heap} (hi : IvarOnly h h') (hch : ChainsIn h) :
    ChainsIn h' := by
  refine ⟨by rw [hi.size]; exact hch.boot, fun o hlt => ?_, fun o hlt e he => ?_,
    fun o cp hlt hcp => ?_⟩
  · rw [hi.size] at hlt ⊢
    rw [hi.klass]
    exact hch.klass o hlt
  · rw [hi.size] at hlt ⊢
    rw [hi.eigen] at he
    exact hch.eigen o hlt e he
  · rw [hi.size] at hlt
    rw [hi.classPayload] at hcp
    obtain ⟨h1, h2, h3⟩ := hch.chain o cp hlt hcp
    exact ⟨fun sc hs => by rw [hi.size]; exact h1 sc hs,
      fun i hi2 => by rw [hi.size]; exact h2 i hi2,
      fun q hq => by rw [hi.size]; exact h3 q hq⟩

/-! ## 1. Saturation, and the fuel monotonicity it buys -/

/-- **The ancestor walk has finished before its fuel runs out.** Stated as "one
    more unit changes nothing" rather than as a bound on the walk's length,
    because that is the weakest form the congruence needs and the only form that
    is true of a heap whose ids do not descend (see the header).

    Both walks are named: `ancestors.go` recurses on its own fuel, and the
    `modAncestors h` it splices in carries a *second* fuel — `h.objs.size + 1`
    again — which a growing heap moves as well. Missing that is how a "one fuel
    lemma" turns into two. -/
def Saturated (h : Heap) : Prop :=
  (∀ mo, modAncestors.go h mo (h.objs.size + 1) = modAncestors.go h mo h.objs.size) ∧
    (∀ k, ancestors.go h k (h.objs.size + 1) = ancestors.go h k h.objs.size)

/-- **Any fuel at or above the heap's own computes the same module walk.** The
    induction is on the *excess* `d` rather than on `f` with `h.objs.size + 1 ≤ f`,
    because `Nat.le_induction` is Mathlib's and this tree depends on core only; the
    `≤` form is the wrapper below.

    The step is the whole argument, and it is two rewrites: unfold both sides once,
    and the recursive calls become `go i (size + 1 + d)` against `go i size`. The
    inductive hypothesis carries the first to `go i (size + 1)` and the *saturation
    clause* carries that to `go i size` — which is the only place saturation is
    used, and the reason it has to be a hypothesis rather than a consequence. -/
theorem modAncestors_go_add {h : Heap}
    (hm : ∀ mo, modAncestors.go h mo (h.objs.size + 1) = modAncestors.go h mo h.objs.size) :
    ∀ (d : Nat) (mo : ObjId),
      modAncestors.go h mo (h.objs.size + 1 + d) = modAncestors.go h mo (h.objs.size + 1) := by
  intro d
  induction d with
  | zero => intro mo; rfl
  | succ d ih =>
    intro mo
    -- The recursive calls sit under a `flatMap`, so the pointwise IH has to be
    -- turned into an equality of *functions* before `simp` can use it — the same
    -- reason `modAncestors_funext` exists.
    have hfun : (fun i => modAncestors.go h i (h.objs.size + 1 + d)) =
        (fun i => modAncestors.go h i h.objs.size) := funext (fun i => (ih i).trans (hm i))
    show modAncestors.go h mo (h.objs.size + 1 + d + 1) = _
    simp only [modAncestors.go, hfun]

theorem modAncestors_go_ge {h : Heap}
    (hm : ∀ mo, modAncestors.go h mo (h.objs.size + 1) = modAncestors.go h mo h.objs.size)
    {f : Nat} (hf : h.objs.size + 1 ≤ f) (mo : ObjId) :
    modAncestors.go h mo f = modAncestors.go h mo (h.objs.size + 1) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hf
  exact modAncestors_go_add hm d mo

/-- The same for the class walk, and shorter: `ancestors.go`'s own fuel is spent
    only on the **superclass** recursion, because the `prepends`/`includes` splices
    call `modAncestors h`, whose fuel is fixed by the heap rather than by this
    parameter. Two fuels in one walk is what makes this two lemmas. -/
theorem ancestors_go_add {h : Heap}
    (ha : ∀ k, ancestors.go h k (h.objs.size + 1) = ancestors.go h k h.objs.size) :
    ∀ (d : Nat) (k : ObjId),
      ancestors.go h k (h.objs.size + 1 + d) = ancestors.go h k (h.objs.size + 1) := by
  intro d
  induction d with
  | zero => intro k; rfl
  | succ d ih =>
    intro k
    have hstep : ∀ s, ancestors.go h s (h.objs.size + 1 + d) = ancestors.go h s h.objs.size :=
      fun s => (ih s).trans (ha s)
    show ancestors.go h k (h.objs.size + 1 + d + 1) = _
    simp only [ancestors.go, hstep]

theorem ancestors_go_ge {h : Heap}
    (ha : ∀ k, ancestors.go h k (h.objs.size + 1) = ancestors.go h k h.objs.size)
    {f : Nat} (hf : h.objs.size + 1 ≤ f) (k : ObjId) :
    ancestors.go h k f = ancestors.go h k (h.objs.size + 1) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hf
  exact ancestors_go_add ha d k

/-! ## 2. The certificate

`Saturated` quantifies over every `ObjId`, and a `Bool` cannot. It does not have
to: out of bounds `classPayload?` is `none` (`classPayload?_oob`), so both walks
answer `[k]` at any positive fuel and the clause holds for free. The `Bool` checks
the ids the heap actually has, and `saturatedB_sound` supplies the rest.
-/

/-! `saturatedB` — the clause as a `Bool` — lives in `RubyCore/HeapCert.lean`, beside
`heapOkB`, and L148 folded it *into* `heapOkB`. Both moves are for the reason F0's
certificate is there: the probe has to compute the predicate the theorem is about
rather than a copy of it, and there is now one heap certificate rather than two. -/

/-- Out of bounds, both walks are `[k]` at **any** positive fuel: there is no
    payload to recurse through, so the fuel is never spent. -/
theorem go_oob (h : Heap) (k : ObjId) (hk : ¬ k < h.objs.size) (f : Nat) :
    modAncestors.go h k (f + 1) = [k] ∧ ancestors.go h k (f + 1) = [k] := by
  have hp := classPayload?_oob h k hk
  refine ⟨?_, ?_⟩ <;> simp only [modAncestors.go, ancestors.go, hp]

/-- So saturation is automatic there, and the `Bool` only has to range over the ids
    the heap actually has. -/
theorem saturated_oob (h : Heap) (hn : 0 < h.objs.size) (k : ObjId)
    (hk : ¬ k < h.objs.size) :
    modAncestors.go h k (h.objs.size + 1) = modAncestors.go h k h.objs.size ∧
      ancestors.go h k (h.objs.size + 1) = ancestors.go h k h.objs.size := by
  obtain ⟨m, hm⟩ : ∃ m, h.objs.size = m + 1 := ⟨h.objs.size - 1, by omega⟩
  refine ⟨?_, ?_⟩
  · rw [(go_oob h k hk h.objs.size).1, hm, (go_oob h k hk m).1]
  · rw [(go_oob h k hk h.objs.size).2, hm, (go_oob h k hk m).2]

theorem saturatedB_sound {h : Heap} (hb : saturatedB h = true) : Saturated h := by
  simp only [saturatedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at hb
  obtain ⟨hn, hall⟩ := hb
  refine ⟨fun mo => ?_, fun k => ?_⟩
  · by_cases hk : mo < h.objs.size
    · exact (hall mo (List.mem_range.mpr hk)).1
    · exact (saturated_oob h hn mo hk).1
  · by_cases hk : k < h.objs.size
    · exact (hall k (List.mem_range.mpr hk)).2
    · exact (saturated_oob h hn k hk).2

/-! ## 3. The congruence, with `≤` where there was `=` -/

/-- The module walk agrees across a growing heap. Two facts compose: the shape
    congruence holds at *equal* fuel with no size hypothesis at all
    (`modAncestors_go_congr`), and saturation moves the fuel. -/
theorem modAncestors_grow {h h' : Heap} (hs : ShapeAgree h h')
    (hsz : h.objs.size ≤ h'.objs.size)
    (hm : ∀ mo, modAncestors.go h mo (h.objs.size + 1) = modAncestors.go h mo h.objs.size) :
    modAncestors h' = modAncestors h := by
  funext mo
  unfold modAncestors
  rw [modAncestors_go_congr hs (h'.objs.size + 1) mo]
  exact modAncestors_go_ge hm (Nat.succ_le_succ hsz) mo

/-- `ancestors_go_congr` with the size equality replaced by `≤` plus saturation.
    The proof is that lemma's, with one substitution: `modAncestors_funext hs hsz`
    becomes `modAncestors_grow hs hsz hm`. Worth noting how *little* the argument
    moves — the fuel was the only thing the size hypothesis was ever doing, which
    is what made pricing this rung by reading the lemma so misleading. -/
theorem ancestors_go_congr_grow {h h' : Heap} (hs : ShapeAgree h h')
    (hsz : h.objs.size ≤ h'.objs.size)
    (hm : ∀ mo, modAncestors.go h mo (h.objs.size + 1) = modAncestors.go h mo h.objs.size) :
    ∀ (fuel : Nat) (k : ObjId), ancestors.go h' k fuel = ancestors.go h k fuel := by
  intro fuel
  induction fuel with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    unfold ancestors.go
    have hk := hs k
    cases h1 : h'.classPayload? k with
    | none =>
      cases h2 : h.classPayload? k with
      | none => simp
      | some c => rw [h1, h2] at hk; exact absurd hk (by simp)
    | some c' =>
      cases h2 : h.classPayload? k with
      | none => rw [h1, h2] at hk; exact absurd hk (by simp)
      | some c =>
        rw [h1, h2] at hk
        simp only [Option.map_some, Option.some.injEq, clsShape, Prod.mk.injEq] at hk
        obtain ⟨hpre, hinc, hsup⟩ := hk
        simp only [hpre, hinc, hsup, modAncestors_grow hs hsz hm, ih]

/-- **The payoff: the ancestor chain survives an allocating step.** `=` became `≤`,
    at the price of one clause about the heap in hand — checkable by
    `saturatedB`, measured by `scripts/probes/ancestors_probe.lean`, and true at the
    prelude-booted heap.

    `ShapeAgree` is unrelativized, which is exactly right for allocating a **plain
    object** (the producer for `.cls C`) and exactly wrong for allocating a
    **class** (`classDef`); the header says what the latter owes. -/
theorem ancestors_congr_grow {h h' : Heap} (hs : ShapeAgree h h')
    (hsz : h.objs.size ≤ h'.objs.size) (hsat : Saturated h) (k : ObjId) :
    ancestors h' k = ancestors h k := by
  unfold ancestors
  rw [ancestors_go_congr_grow hs hsz hsat.1 (h'.objs.size + 1) k,
    ancestors_go_ge hsat.2 (Nat.succ_le_succ hsz) k]

/-! ## 4. Saturation is itself preserved (L148)

`Saturated` is about to become a conjunct of the machine invariant, because
`DeclsOk_grow` needs it at the step and only the invariant can carry it there. So it
owes what every conjunct owes: a proof for each step that writes the heap. There are
two shapes, and both are corollaries of congruences that already exist.
-/

/-- **A method-table write cannot make the walk fuel-sensitive.** `defineMethod`
    preserves the shape *and* the size, so `go` agrees at every fuel and saturation
    transports by rewriting three times. -/
theorem Saturated_defineMethod {h : Heap} (hsat : Saturated h) (cls : ObjId)
    (name : String) (md : MethodDef) : Saturated (defineMethod h cls name md) := by
  have hs : ShapeAgree h (defineMethod h cls name md) :=
    fun j => shape_defineMethod h cls j name md
  have hsz := objs_size_defineMethod h cls name md
  refine ⟨fun mo => ?_, fun k => ?_⟩
  · rw [hsz, modAncestors_go_congr hs _ mo, modAncestors_go_congr hs _ mo]
    exact hsat.1 mo
  · rw [hsz, ancestors_go_congr hs hsz _ k, ancestors_go_congr hs hsz _ k]
    exact hsat.2 k

/-- **Nor can an allocation**, and this one is the interesting direction: the fuel
    *changes*, so the proof is the fuel monotonicity of §1 rather than a rewrite.
    Both walks agree with the old heap's at any fuel (shape congruence, which needs no
    size hypothesis), and above `objs.size + 1` the old heap's answer no longer moves —
    so the new heap's does not either, at its own larger fuel. -/
theorem Saturated_grow {h h' : Heap} (hg : ShapeAgree h h')
    (hsz : h.objs.size ≤ h'.objs.size) (hsat : Saturated h) : Saturated h' := by
  have key : ∀ f, h.objs.size ≤ f → ∀ k,
      modAncestors.go h k f = modAncestors.go h k (h.objs.size + 1) ∧
        ancestors.go h k f = ancestors.go h k (h.objs.size + 1) := by
    intro f hf k
    rcases Nat.lt_or_ge f (h.objs.size + 1) with hlt | hge
    · -- `f = objs.size` is the only case below the threshold, and it is saturation itself.
      have : f = h.objs.size := by omega
      subst this
      exact ⟨(hsat.1 k).symm, (hsat.2 k).symm⟩
    · exact ⟨modAncestors_go_ge hsat.1 hge k, ancestors_go_ge hsat.2 hge k⟩
  refine ⟨fun mo => ?_, fun k => ?_⟩
  · rw [modAncestors_go_congr hg _ mo, modAncestors_go_congr hg _ mo,
      (key _ (Nat.le_trans hsz (Nat.le_succ _)) mo).1, (key _ hsz mo).1]
  · rw [ancestors_go_congr_grow hg hsz hsat.1 _ k, ancestors_go_congr_grow hg hsz hsat.1 _ k,
      (key _ (Nat.le_trans hsz (Nat.le_succ _)) k).2, (key _ hsz k).2]

/-! ~~`shapeAgree_alloc_nonClass`~~ is **withdrawn** (L150). It said a non-class
`Heap.alloc` preserves every shape; L145's `plainGrow_alloc` says strictly more (the
whole `classPayload?` function agrees, not only its `clsShape`), and `PlainGrow.shapeAgree`
recovers this. Two lemmas about the same step, one of them weaker, is how a reader ends up
proving the weaker thing. -/

end Proof
end RubyCore
