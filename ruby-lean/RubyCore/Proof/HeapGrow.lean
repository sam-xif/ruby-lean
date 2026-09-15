import RubyCore.Proof.AncestorsGrow
import RubyCore.Proof.BuiltinConformance

/-!
# What an allocating step leaves alone (L145, producer's bill items 4–5)

L143 relativized the *type* transport (`TypeAgree`) and L144 the *ancestor* walk.
What is still missing before a producer can have a consecution case is the
**resolution** transport: `DeclsOk`'s heap-dependent half is `ResolvesTo`, which
reads `lookup`, `ancestors`, `classOf`, `className` and `crubyShadow`, and every
one of those has to answer the same in the post-allocation heap or the invariant
does not survive the step.

## One notion, and why it is stated per-field rather than as an equality

`PlainGrow h h'` is what pushing a **non-class** object supplies:

* the heap only grows;
* every id the old heap had reads back identically — so method tables, `klass`,
  `eigen` and payloads of existing objects are all untouched;
* `classPayload?` agrees at **every** id, including the new ones.

The third clause is the one that does the work, and it is why this rung is about
*plain* objects. `classPayload?` is what `lookup`, `ancestors`, `className` and
`crubyShadow` all read, and a non-class allocation leaves it `none` at the fresh id
in both heaps — so agreement is **global** rather than relativized, and none of the
congruences below need to know that the walk stays inside the old heap. Allocating a
**class** breaks exactly that clause and nothing else, which is the honest statement
of what `classDef` will owe (`AncestorsGrow.lean`'s header, and the
`0 out-of-bounds edges` line of `scripts/probes/ancestors_probe.lean`).

## What this file does *not* claim

Nothing here says the invariant is preserved. It says the *resolution* half is, and
that is the half that is a fact about the heap. The conformance half is
`ConformsAt`, whose hypotheses read the heap the wrong way round for a growing step
(it needs `ValueTy h recv τr` where the new heap supplies `ValueTy h' recv τr`), and
repairing that means changing what conformance *says* rather than proving another
congruence — the next commit.
-/

namespace RubyCore
namespace Proof

open Interp

/-- **What an `alloc` of a non-class object leaves alone.** A structure rather than
    a conjunction because three of the four consumers want a different field, and
    projections read better than `.2.2.1` at the use site (L140's lesson about
    `DeclsOk`'s split, applied to a hypothesis). -/
structure PlainGrow (h h' : Heap) : Prop where
  /-- The heap only grows. -/
  size : h.objs.size ≤ h'.objs.size
  /-- Every id the old heap had reads back identically. -/
  get : ∀ o, o < h.objs.size → h'.get o = h.get o
  /-- And nothing anywhere became a class. -/
  payload : ∀ k, h'.classPayload? k = h.classPayload? k
  /-- **J43: a fresh object's dispatch fields are bounded and inert** — its
      `klass` is an id the *old* heap had and it carries no eigenclass. What
      `ChainsIn` needs re-established across an abstract `PlainGrow` (the
      dispatch lemmas expose no fields of what a builtin allocated), and true of
      every producer for `freshIvars`'s reason: the fragment's allocations are
      literals, whose classes are boot ids. -/
  freshKlass : ∀ o, h.objs.size ≤ o → o < h'.objs.size →
    (h'.get o).klass < h.objs.size ∧ (h'.get o).eigen = none
  /-- **And a fresh object has no instance variables** (L196). Not hygiene: `IvarOk`
      is quantified over *every* object of a class, so an allocation could break a row
      by producing an instance with a badly-typed `@x`, and nothing else in `PlainGrow`
      bounds the fresh slots. Every allocation the fragment performs is a *literal* —
      a String or an Array — and a literal has no ivars, so the clause is `rfl` at both
      call sites; it is a clause rather than a free consequence because `Class.new`
      (Wall 2) is where it stops being one. -/
  freshIvars : ∀ o, h.objs.size ≤ o → (h'.get o).ivars = []

/-- **Reflexivity** (L215), which is what makes an allocating `ConformsAt` a strict
    generalization: every witness that leaves the machine alone supplies this and reads
    exactly as it did. `freshIvars` is vacuous because `h.objs.size ≤ o` puts `o` out of
    bounds and `Heap.get` answers the default object there, whose `ivars` is `[]`. -/
theorem PlainGrow.rfl' (h : Heap) : PlainGrow h h :=
  { size := Nat.le_refl _
    get := fun _ _ => rfl
    payload := fun _ => rfl
    freshKlass := fun o ho ho' => absurd ho' (by omega)
    freshIvars := fun o ho => by
      simp only [Heap.get, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none (by omega), Option.getD_none]
      rfl }

/-- Pushing a non-class object is an instance. The `payload` clause is where the
    non-class hypothesis is spent: at the fresh id both heaps answer `none`, in one
    case because the object is not a class and in the other because it is not
    there. -/
theorem plainGrow_alloc (h : Heap) (obj : Object) (hnc : ∀ c, obj.payload ≠ .cls c)
    (hiv : obj.ivars = [])
    (hkl : obj.klass < h.objs.size := by decide)
    (heig : obj.eigen = none := by rfl) :
    PlainGrow h ⟨h.objs.push obj⟩ := by
  have hget : ∀ o, o < h.objs.size → (Heap.get ⟨h.objs.push obj⟩ o) = h.get o := by
    intro o ho
    simp only [Heap.get, Array.getD_eq_getD_getElem?, Array.getElem?_push,
      if_neg (Nat.ne_of_lt ho)]
  have hgnew : (Heap.get ⟨h.objs.push obj⟩ h.objs.size) = obj := by
    simp [Heap.get, Array.getD_eq_getD_getElem?]
  refine ⟨by simp, hget, fun k => ?_, fun o hlo hhi => ?_, fun o ho => ?_⟩
  case refine_2 =>
    have ho : o = h.objs.size := by
      have : o < h.objs.size + 1 := by simpa using hhi
      omega
    subst ho
    rw [hgnew]
    exact ⟨hkl, heig⟩
  case refine_3 =>
    -- Above the old size there is exactly one inhabited slot, and it is `obj`;
    -- anything higher reads `default`, whose `ivars` is `[]` too.
    by_cases he : o = h.objs.size
    · subst he
      rw [show (Heap.get ⟨h.objs.push obj⟩ h.objs.size) = obj from by
        simp [Heap.get, Array.getD_eq_getD_getElem?]]
      exact hiv
    · have hb : ¬ o < (h.objs.push obj).size := by simp; omega
      simp only [Heap.get, Array.getD, dif_neg hb]
      rfl
  by_cases hk : k < h.objs.size
  · simp only [Heap.classPayload?, hget k hk]
  · rw [classPayload?_oob h k hk]
    by_cases he : k = h.objs.size
    · subst he
      have hg : (Heap.get ⟨h.objs.push obj⟩ h.objs.size) = obj := by
        simp [Heap.get, Array.getD_eq_getD_getElem?]
      unfold Heap.classPayload?
      rw [hg]
      cases hpl : obj.payload with
      | cls c => exact absurd hpl (hnc c)
      | _ => rfl
    · refine classPayload?_oob _ k ?_
      have hlt : h.objs.size < k :=
        Nat.lt_of_le_of_ne (Nat.not_lt.mp hk) (fun hEq => he hEq.symm)
      show ¬ k < (h.objs.push obj).size
      rw [Array.size_push]
      exact Nat.not_lt.mpr (Nat.succ_le_of_lt hlt)

/-- **`ChainsIn` survives a plain growth** (J43): old edges by `get`-agreement,
    fresh objects by `freshKlass`, and no fresh id has a payload at all
    (`payload`'s global agreement), so the chain clause never fires there. -/
theorem chainsIn_plainGrow {h h' : Heap} (hg : PlainGrow h h') (hch : ChainsIn h) :
    ChainsIn h' := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := hch.boot
  refine ⟨⟨Nat.lt_of_lt_of_le b1 hg.size, Nat.lt_of_lt_of_le b2 hg.size,
      Nat.lt_of_lt_of_le b3 hg.size, Nat.lt_of_lt_of_le b4 hg.size,
      Nat.lt_of_lt_of_le b5 hg.size⟩,
    fun o hlt => ?_, fun o hlt e he => ?_, fun o cp hlt hcp => ?_⟩
  · by_cases hlo : o < h.objs.size
    · rw [hg.get o hlo]
      exact Nat.lt_of_lt_of_le (hch.klass o hlo) hg.size
    · exact Nat.lt_of_lt_of_le
        ((hg.freshKlass o (Nat.le_of_not_lt hlo) hlt).1) hg.size
  · by_cases hlo : o < h.objs.size
    · rw [hg.get o hlo] at he
      exact Nat.lt_of_lt_of_le (hch.eigen o hlo e he) hg.size
    · rw [(hg.freshKlass o (Nat.le_of_not_lt hlo) hlt).2] at he
      exact absurd he (by simp)
  · by_cases hlo : o < h.objs.size
    · have hcp0 : h.classPayload? o = some cp := by rw [← hg.payload o]; exact hcp
      obtain ⟨h1, h2, h3⟩ := hch.chain o cp hlo hcp0
      exact ⟨fun sc hs => Nat.lt_of_lt_of_le (h1 sc hs) hg.size,
        fun i hi => Nat.lt_of_lt_of_le (h2 i hi) hg.size,
        fun q hq => Nat.lt_of_lt_of_le (h3 q hq) hg.size⟩
    · rw [hg.payload o, classPayload?_oob h o hlo] at hcp
      exact absurd hcp (by simp)

/-! ## 1. The pure object-model functions

Named `_eq` rather than after the function they are about, because inside
`namespace RubyCore.Proof` a theorem called `PlainGrow.className` shadows
`className` in every later proof in the file.
-/

theorem PlainGrow.shapeAgree {h h' : Heap} (hg : PlainGrow h h') : ShapeAgree h h' :=
  fun k => by rw [hg.payload k]

theorem PlainGrow.className_eq {h h' : Heap} (hg : PlainGrow h h') (k : ObjId) :
    className h' k = className h k := by
  simp only [className, hg.payload k]

/-- `classOf` needs the id to be one the old heap had — it is the one function here
    that reads the object rather than its payload, and the fresh id is exactly where
    it disagrees (`scripts/probes/alloc_probe.lean`). -/
theorem PlainGrow.classOf_eq {h h' : Heap} (hg : PlainGrow h h') {o : ObjId}
    (ho : o < h.objs.size) : classOf h' (.ref o) = classOf h (.ref o) := by
  simp only [classOf, hg.get o ho]

theorem PlainGrow.classOf_value_eq {h h' : Heap} (hg : PlainGrow h h') (v : Value)
    (hv : ∀ o, v = .ref o → o < h.objs.size) : classOf h' v = classOf h v := by
  cases v with
  | ref o => exact hg.classOf_eq (hv o rfl)
  | bool b => cases b <;> rfl
  | _ => rfl

theorem PlainGrow.ancestors_eq {h h' : Heap} (hg : PlainGrow h h') (hsat : Saturated h)
    (k : ObjId) : ancestors h' k = ancestors h k :=
  ancestors_congr_grow hg.shapeAgree hg.size hsat k

/-! ## 2. Resolution: `lookup` and the shadow gate -/

/-- The method-table walk, one ancestor at a time. `lookup.go` reads only
    `classPayload?`, which `PlainGrow` pins **everywhere**, so this needs no side
    condition on the chain — and that is precisely what the non-class restriction
    buys. -/
theorem lookup_go_grow {h h' : Heap} (hg : PlainGrow h h') (mname : String) :
    ∀ chain, lookup.go h' mname chain = lookup.go h mname chain := by
  intro chain
  induction chain with
  | nil => rfl
  | cons k rest ih =>
    unfold lookup.go
    rw [hg.payload k]
    split <;> simp [ih]

theorem lookup_grow {h h' : Heap} (hg : PlainGrow h h') (hsat : Saturated h)
    {recv : Value} (hrv : ∀ o, recv = .ref o → o < h.objs.size) (mname : String) :
    lookup h' recv mname = lookup h recv mname := by
  unfold lookup
  rw [hg.classOf_value_eq recv hrv, hg.ancestors_eq hsat, lookup_go_grow hg]

/-- The CRuby shadow gate reads `className` over a chain and nothing else, so
    `PlainGrow`'s global `className` agreement settles it for **any** chain — there
    is no need to know the chain came from an old heap's walk. Same one-line shape
    as `crubyShadow_defineMethod`. -/
theorem crubyShadow_grow {h h' : Heap} (hg : PlainGrow h h') (chain : List ObjId)
    (mname : String) : crubyShadow h' chain mname = crubyShadow h chain mname := by
  unfold crubyShadow
  simp only [hg.className_eq]

end Proof
end RubyCore
