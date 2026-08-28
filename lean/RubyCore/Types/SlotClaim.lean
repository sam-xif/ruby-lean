import RubyCore.Heap
import RubyCore.Types.Decls

/-!
# SF — the slot frame: local heap stability as a first-order resource algebra

`docs/semantics/slot-frame.md`. Decisions are **SF-numbers** and are cited inline.

The one sentence: every typing fact is a claim about a mutable method table, and
until now the *only* answer to "why is this still true after the program runs?"
was the name-global sledgehammer (`declaresName`, `Decls.lean:329`). This file
gives the local answer — a claim owns **slots**, composition is disjoint union
with agreement, and a write conflicts with a claim only if it lands on a slot,
spine or default the claim actually reads (SF8).

Everything here is **data plus one kernel `Bool`** (§7.2 fixed point): the
semantic reading `SlotClaim.Holds` is a `Prop`, the checker `SlotClaim.holdsB` is
a `Bool`, and `holdsB_iff` is the bridge the frame theorems are stated over.

## Layering

* SF1/SF2 — `slotOf`, the three primitive facts (`SlotDefined`/`SlotEmpty`/`NoMM`).
* SF3/SF4 — `Spine`: resolution is a projection over `ancestors`, so a claim owns
  a *prefix* of it as a value.
* SF5/SF6 — `SlotClaim` + `compose`: the PCM. Reads are duplicable; writes are
  not resources at all, they are enumerated (`Install`).
* SF8 — `Install.conflicts`, the write rule, as its table.

The frame theorems live in `RubyCore/Proof/Static/Frame.lean` (SF-T1/SF-T2).
-/

namespace RubyCore.Types

open RubyCore

/-! ## SF1 — a class is a slot map with a default -/

/-- **The slot.** `(K, m)`'s content in `h`: the class's own table entry, no walk.
    `none` covers both "no such entry" and "not a class at all" — the second is
    inert for every purpose here, since a non-class id has no table to write. -/
def slotOf (h : Heap) (k : ObjId) (m : String) : Option MethodDef :=
  (h.classPayload? k).bind fun c => (c.methods.find? (·.1 == m)).map (·.2)

/-- SF1, row 1 — **the slot is filled, with something of the declared shape.**

    Deliberately *not* full conformance: this predicate is the frame's business
    (what a write can break), and the body's semantic conformance is the existing
    `EntryOkJ`/`ConformsAt` line's. What is recorded is exactly the part a claim
    must re-check when it composes: arity, liveness, visibility. -/
def SlotDefined (h : Heap) (k : ObjId) (m : String) (d : MethodDecl) : Prop :=
  ∃ md, slotOf h k m = some md ∧
    md.params.length = d.params.length ∧
    md.undefined = false ∧
    md.visibility = .pub

/-- SF1, row 2 — **the slot is known empty.** The ownable form of the negative
    fact the shadow clause needs: absence at *this* cell, so the absence a
    resolution depends on decomposes along the chain into cell-wise resources. -/
def SlotEmpty (h : Heap) (k : ObjId) (m : String) : Prop :=
  slotOf h k m = none

/-- SF1, row 3 / SF2 — **the default component is inert.** `method_missing` is a
    write to `default(K)`, not to any named slot: it fills every unfilled slot at
    once, so it invalidates every `SlotEmpty` reader on a chain through `K` and no
    `SlotDefined` reader at all. Owning `NoMM K` is what makes those `SlotEmpty`
    readers stable.

    Note this is a genuinely *new* obligation — `hookFreeNames` omits
    `method_missing` (soundly, while nothing owns emptiness). SF8 prices it. -/
def NoMM (h : Heap) (k : ObjId) : Prop :=
  slotOf h k "method_missing" = none

/-! ## SF3/SF4 — the chain shape is itself a resource -/

/-- SF4 — **`spine C seg`**: `seg` is a prefix of `C`'s ancestor chain, as a
    value. Resolution is the front-slot-wins fold over that list (SF3), so a `Row`
    claim owns the prefix from `C` down to the owner. A reader is invalidated by
    `include`/`prepend`/`extend` landing anywhere on the segment — the
    linked-list-spliced-from-outside case — which is exactly `Install.ancestry`. -/
def Spine (h : Heap) (k : ObjId) (seg : List ObjId) : Prop :=
  seg.isPrefixOf (ancestors h k) = true

/-! ## SF5 — the resources, as a partial commutative monoid -/

/-- SF5 — one claim's footprint: what it reads. All four components are read-only
    (SF6), which is what keeps this first-order: composition never has to *move*
    ownership, only check that two readers can coexist.

    This is the gmap-RA shape — if the flip condition in §8 of the design ever
    fires, the Iris lift is mechanical. -/
structure SlotClaim where
  /-- Filled slots, with the declared shape. **Agreement required on overlap.** -/
  defined : List (ObjId × String × MethodDecl) := []
  /-- Known-empty slots. Freely duplicable. -/
  empty : List (ObjId × String) := []
  /-- Owned ancestor prefixes (SF4). Agreement on overlap: two claims about the
      same class's spine must be prefix-compatible, which for a *prefix of the
      same list* means one extends the other. -/
  spines : List (ObjId × List ObjId) := []
  /-- Classes whose default component is known inert (SF2). Duplicable. -/
  noMM : List ObjId := []
deriving Repr, Inhabited, DecidableEq

namespace SlotClaim

/-- The unit of the monoid: reads nothing, framed by every write. -/
def unit : SlotClaim := {}

/-- Prefix-compatibility of two owned segments of the *same* class: one is a
    prefix of the other. Both are prefixes of one `ancestors` list, so this is
    exactly agreement (and is what `compose` must check to stay a PCM). -/
def segCompat (a b : List ObjId) : Bool :=
  a.isPrefixOf b || b.isPrefixOf a

/-- The longer of two compatible segments — the composed spine claim. -/
def segJoin (a b : List ObjId) : List ObjId :=
  if a.length ≤ b.length then b else a

/-- SF5 — **composition: `defined`-overlap must agree, spines must be
    prefix-compatible, everything else unions. `none` is conflict.** -/
def compose (a b : SlotClaim) : Option SlotClaim :=
  if a.defined.all (fun x => b.defined.all fun y =>
        !(x.1 == y.1 && x.2.1 == y.2.1) || x.2.2 == y.2.2)
     && a.spines.all (fun x => b.spines.all fun y => !(x.1 == y.1) || segCompat x.2 y.2)
  then some
    { defined := a.defined ++ b.defined.filter (fun y => !a.defined.any (fun x =>
                    x.1 == y.1 && x.2.1 == y.2.1))
      empty := a.empty ++ b.empty.filter (fun y => !a.empty.contains y)
      spines := a.spines.map (fun x =>
                    match b.spines.find? (fun y => y.1 == x.1) with
                    | some y => (x.1, segJoin x.2 y.2)
                    | none => x)
                ++ b.spines.filter (fun y => !a.spines.any (fun x => x.1 == y.1))
      noMM := a.noMM ++ b.noMM.filter (fun k => !a.noMM.contains k) }
  else none

/-- The footprint of a certificate: the composition of its `Row`s' claims (SF7).
    `none` at any step is the conflict the validator rejects on (§5 step 1). -/
def composeAll : List SlotClaim → Option SlotClaim
  | [] => some unit
  | c :: rest => (composeAll rest).bind (compose c)

/-! ### The semantic reading, and the kernel `Bool` that decides it -/

/-- What owning the claim *means* at a heap. -/
def Holds (c : SlotClaim) (h : Heap) : Prop :=
  (∀ x ∈ c.defined, SlotDefined h x.1 x.2.1 x.2.2)
  ∧ (∀ x ∈ c.empty, SlotEmpty h x.1 x.2)
  ∧ (∀ x ∈ c.spines, Spine h x.1 x.2)
  ∧ (∀ k ∈ c.noMM, NoMM h k)

/-- Slot shape as a `Bool` — the `SlotDefined` decision. -/
def slotDefinedB (h : Heap) (k : ObjId) (m : String) (d : MethodDecl) : Bool :=
  match slotOf h k m with
  | some md => md.params.length == d.params.length && !md.undefined && md.visibility == .pub
  | none => false

/-- §7.2 — **validation is one kernel `Bool`.** -/
def holdsB (c : SlotClaim) (h : Heap) : Bool :=
  c.defined.all (fun x => slotDefinedB h x.1 x.2.1 x.2.2)
  && c.empty.all (fun x => (slotOf h x.1 x.2).isNone)
  && c.spines.all (fun x => x.2.isPrefixOf (ancestors h x.1))
  && c.noMM.all (fun k => (slotOf h k "method_missing").isNone)

theorem slotDefinedB_iff {h : Heap} {k : ObjId} {m : String} {d : MethodDecl} :
    slotDefinedB h k m d = true ↔ SlotDefined h k m d := by
  unfold slotDefinedB SlotDefined
  cases hs : slotOf h k m with
  | none => simp
  | some md =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
    constructor
    · rintro ⟨⟨hp, hu⟩, hv⟩; exact ⟨md, rfl, hp, hu, by simpa using hv⟩
    · rintro ⟨md', hs', hp, hu, hv⟩
      cases Option.some.inj hs'
      exact ⟨⟨hp, hu⟩, by simp [hv]⟩

/-- The bridge. Both sides are conjunctions of the same four families. -/
theorem holdsB_iff {c : SlotClaim} {h : Heap} : c.holdsB h = true ↔ c.Holds h := by
  unfold holdsB Holds
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Option.isNone_iff_eq_none, slotDefinedB_iff]
  constructor
  · rintro ⟨⟨⟨hd, he⟩, hs⟩, hm⟩
    exact ⟨fun x hx => hd x hx, fun x hx => he x hx, fun x hx => hs x hx, fun k hk => hm k hk⟩
  · rintro ⟨hd, he, hs, hm⟩
    exact ⟨⟨⟨fun x hx => hd x hx, fun x hx => he x hx⟩, fun x hx => hs x hx⟩,
      fun k hk => hm k hk⟩

instance (c : SlotClaim) (h : Heap) : Decidable (c.Holds h) :=
  decidable_of_iff _ holdsB_iff

/-! ## SF7 — `Row` is derived, not primitive -/

/-- SF7 — the assertion the type system consumes, *as a claim*:

    ```
    Row C m σ  ≜  spine C seg ∗ (empty K m ∗ noMM K for each K ∈ seg before owner)
                             ∗ defined owner m σ
    ```

    `seg` is the ancestor prefix from `C` down to and including the owner; the
    owner is its last element. The two measured blockers clear by construction:
    two `Row`s through the same mixin share `defined Comparable "<" σ`
    (agreement, same slot) with disjoint `empty` segments, and a `defined` at a
    class off another `Row`'s chain touches nothing that `Row` reads. -/
def row (C : ObjId) (seg : List ObjId) (owner : ObjId) (m : String)
    (σ : MethodDecl) : SlotClaim :=
  let before := seg.takeWhile (· != owner)
  { defined := [(owner, m, σ)]
    empty := before.map (fun k => (k, m))
    spines := [(C, seg)]
    noMM := before }

end SlotClaim

/-! ## SF8 — the write rule -/

/-- The table-mutating actions the program performs, as enumerated by §5 step 2's
    walk over the linked program. SF6: a writer is not a resource, it is an
    *entry in this inventory*, and the frame check is disjointness against it. -/
inductive Install where
  /-- `def m` / `defs m` / `define_method(:m)` / the write half of `alias` at `K`. -/
  | defM (k : ObjId) (name : String)
  /-- `include` / `prepend` / `extend` at `K`: a write into the projection. -/
  | ancestry (k : ObjId)
  /-- SF6a — **a laundering site**: a write at `K` whose name coordinate is data
      (`define_method(argv[0])`). The site is still enumerable; its key set is ⊤,
      so it conflicts with every reader at `K`. Completeness is lost here by
      design — a rejection flags metaprogramming driven by unvalidated input. -/
  | anyName (k : ObjId)
deriving Repr, Inhabited, DecidableEq

namespace Install

/-- The class an install writes to. -/
def target : Install → ObjId
  | .defM k _ => k
  | .ancestry k => k
  | .anyName k => k

/-- SF8's table, as a decision. Note the first row prices **additions**, not just
    redefinitions: a fresh `def to_s` at `Version` conflicts with a `Row` that
    resolves `to_s` at `Object` through `Version`, because `Version` is on that
    `Row`'s own `empty` segment. `declaresName`'s "additions are free" was true
    only of the four-row table it guarded. -/
def conflicts (i : Install) (c : SlotClaim) : Bool :=
  match i with
  | .defM k name =>
    c.defined.any (fun x => x.1 == k && x.2.1 == name)
    || c.empty.any (fun x => x.1 == k && x.2 == name)
    -- SF2: `def method_missing` is a write to the default component.
    || (name == "method_missing" && c.noMM.contains k)
  | .ancestry k => c.spines.any (fun x => x.2.contains k)
  | .anyName k =>
    c.defined.any (fun x => x.1 == k)
    || c.empty.any (fun x => x.1 == k)
    || c.noMM.contains k

end Install

/-- §5 step 3 — **the conflict check**: no enumerated install lands on anything
    the composed footprint reads. This is the hypothesis the frame theorems
    (`Proof/Static/Frame.lean`) consume, and it is `decide`-able by construction. -/
def framedB (c : SlotClaim) (is : List Install) : Bool :=
  is.all fun i => !i.conflicts c

end RubyCore.Types
