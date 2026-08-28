import RubyCore.Proof.Static.Decls
import RubyCore.Types.SlotClaim

/-!
# SF-T1/SF-T2 — the frame rule for one step

`docs/semantics/slot-frame.md` §6. The design puts SF-T1 first on purpose: it is
**the frame rule for one step**, and it is where the design meets the shadow
clause. If it fights, we find out in one lemma rather than after a layer.

It did not fight. The whole content is two elementary facts about `lookup.go`:

* `lookup_go_prefix` — resolution that succeeds on a *prefix* of the chain
  succeeds identically on the chain (front slot wins, SF3);
* `lookup_go_off` — a `defineMethod` at a class **not on the walked list** is
  invisible to the walk, whatever the name.

Together: a write is framed by a resolution that already completed *before* the
written class. That is strictly weaker than the name-disjointness the existing
`ResolvesAt_defineMethod` demands — which is now recovered as the special case
where the walked prefix is the whole chain (`ResolvesAt_defineMethod` still
stands unchanged; this is its local sibling, not its replacement).

The shadow clause costs nothing: `crubyShadow` reads only `className`, so
`crubyShadow_defineMethod` is unconditional. The `empty`-segment resource and the
shadow gate decompose over the *same* segment, which is what §6 wanted checked.
-/

namespace RubyCore
namespace Proof
namespace Static

open RubyCore.Types

/-! ## The two walk lemmas -/

/-- Front slot wins (SF3): a hit on a prefix is the hit on the whole chain. -/
theorem lookup_go_prefix {h : Heap} {m : String} {pre chain : List ObjId}
    (hp : pre <+: chain) {r : ObjId × MethodDef}
    (hl : lookup.go h m pre = some r) : lookup.go h m chain = some r := by
  induction pre generalizing chain with
  | nil => exact absurd hl (by simp [lookup.go])
  | cons k rest ih =>
    obtain ⟨t, rfl⟩ := hp
    rw [List.cons_append]
    unfold lookup.go at hl ⊢
    cases hc : h.classPayload? k with
    | none => rw [hc] at hl; exact ih ⟨t, rfl⟩ hl
    | some c =>
      rw [hc] at hl
      dsimp only at hl ⊢
      cases hf : c.methods.find? (·.1 == m) with
      | none => rw [hf] at hl; simp only [hf]; exact ih ⟨t, rfl⟩ hl
      | some e => rw [hf] at hl; simp only [hf]; exact hl

/-- The payload of a class the write did not target is untouched. The `k ≠ cls`
    branch of `shape_defineMethod`, kept whole instead of projected. -/
theorem classPayload?_defineMethod_ne (h : Heap) (cls k : ObjId) (name : String)
    (md : MethodDef) (hk : k ≠ cls) :
    (defineMethod h cls name md).classPayload? k = h.classPayload? k := by
  unfold defineMethod
  split
  · simp only [Heap.setClassPayload, Heap.classPayload?, Heap.get, Heap.set]
    rw [objs_getD_set!_ne _ _ _ _ hk]
  · rfl

/-- **Off-chain writes are invisible to the walk**, for *any* name — the half of
    SF-T1 that name-disjointness cannot express. -/
theorem lookup_go_off {h : Heap} {cls : ObjId} {name m : String} {md : MethodDef}
    {chain : List ObjId} (hoff : cls ∉ chain) :
    lookup.go (defineMethod h cls name md) m chain = lookup.go h m chain := by
  induction chain with
  | nil => rfl
  | cons k rest ih =>
    have hk : k ≠ cls := fun hh => hoff (by simp [hh])
    have hrest : cls ∉ rest := fun hh => hoff (by simp [hh])
    unfold lookup.go
    rw [classPayload?_defineMethod_ne h cls k name md hk]
    cases h.classPayload? k with
    | none => exact ih hrest
    | some c => dsimp only; split <;> simp [ih hrest]

/-- `takeWhile (· != cls)` never contains `cls`. -/
theorem not_mem_takeWhile_ne {cls : ObjId} {l : List ObjId} :
    cls ∉ l.takeWhile (· != cls) := by
  induction l with
  | nil => simp
  | cons k rest ih =>
    by_cases hk : k != cls
    · simp only [List.takeWhile_cons, hk, if_true, List.mem_cons, not_or]
      exact ⟨fun hh => by simp [hh] at hk, ih⟩
    · simp [List.takeWhile_cons, hk]

/-- The class a walk stops at really has the slot filled. -/
theorem lookup_go_slot {h : Heap} {m : String} {chain : List ObjId} {r : ObjId × MethodDef}
    (hl : lookup.go h m chain = some r) : slotOf h r.1 m = some r.2 := by
  induction chain with
  | nil => exact absurd hl (by simp [lookup.go])
  | cons k rest ih =>
    unfold lookup.go at hl
    cases hc : h.classPayload? k with
    | none => rw [hc] at hl; exact ih hl
    | some c =>
      rw [hc] at hl; dsimp only at hl
      cases hf : c.methods.find? (·.1 == m) with
      | none => rw [hf] at hl; exact ih hl
      | some e =>
        rw [hf] at hl
        cases hl
        simp [slotOf, hc, hf]

/-- And it is on the chain. -/
theorem lookup_go_mem {h : Heap} {m : String} {chain : List ObjId} {r : ObjId × MethodDef}
    (hl : lookup.go h m chain = some r) : r.1 ∈ chain := by
  induction chain with
  | nil => exact absurd hl (by simp [lookup.go])
  | cons k rest ih =>
    unfold lookup.go at hl
    cases hc : h.classPayload? k with
    | none => rw [hc] at hl; exact List.mem_cons_of_mem _ (ih hl)
    | some c =>
      rw [hc] at hl; dsimp only at hl
      cases hf : c.methods.find? (·.1 == m) with
      | none => rw [hf] at hl; exact List.mem_cons_of_mem _ (ih hl)
      | some e => rw [hf] at hl; cases hl; simp

/-- Front-slot-wins, backwards: a hit whose owner lies inside a prefix is the
    prefix's hit too. -/
theorem lookup_go_of_prefix_mem {h : Heap} {m : String} {pre chain : List ObjId}
    (hp : pre <+: chain) {r : ObjId × MethodDef}
    (hl : lookup.go h m chain = some r) (hmem : r.1 ∈ pre) :
    lookup.go h m pre = some r := by
  induction pre generalizing chain with
  | nil => exact absurd hmem (by simp)
  | cons k rest ih =>
    obtain ⟨t, rfl⟩ := hp
    rw [List.cons_append] at hl
    unfold lookup.go at hl ⊢
    cases hc : h.classPayload? k with
    | none =>
      rw [hc] at hl
      have hk : r.1 ≠ k := by
        intro hh; have := lookup_go_slot hl; rw [hh] at this; simp [slotOf, hc] at this
      exact ih ⟨t, rfl⟩ hl ((List.mem_cons.mp hmem).resolve_left hk)
    | some c =>
      rw [hc] at hl; dsimp only at hl ⊢
      cases hf : c.methods.find? (·.1 == m) with
      | none =>
        rw [hf] at hl
        have hk : r.1 ≠ k := by
          intro hh; have := lookup_go_slot hl; rw [hh] at this; simp [slotOf, hc, hf] at this
        exact ih ⟨t, rfl⟩ hl ((List.mem_cons.mp hmem).resolve_left hk)
      | some e => rw [hf] at hl; exact hl

/-- A prefix avoiding `cls` stays inside `takeWhile (· != cls)`. -/
theorem prefix_takeWhile_of_not_mem {cls : ObjId} {p l : List ObjId}
    (hp : p <+: l) (hm : cls ∉ p) : p <+: l.takeWhile (· != cls) := by
  induction p generalizing l with
  | nil => simp
  | cons k rest ih =>
    obtain ⟨t, ht⟩ := hp
    subst ht
    have hk : (k != cls) = true := by
      simp only [bne_iff_ne, ne_eq]; intro hh; exact hm (by simp [hh])
    have hrest : cls ∉ rest := fun hh => hm (List.mem_cons_of_mem _ hh)
    rw [List.cons_append]
    simp only [List.takeWhile_cons, hk, if_true]
    obtain ⟨u, hu⟩ := ih (l := rest ++ t) ⟨t, rfl⟩ hrest
    exact ⟨u, by simp [hu]⟩

/-- The segment down to and including a member is a prefix of the list. -/
theorem takeWhile_append_prefix {x : ObjId} {l : List ObjId} (hx : x ∈ l) :
    l.takeWhile (· != x) ++ [x] <+: l := by
  induction l with
  | nil => exact absurd hx (by simp)
  | cons k rest ih =>
    by_cases hk : k = x
    · subst hk; exact ⟨rest, by simp⟩
    · have hb : (k != x) = true := by simp [hk]
      have hx' : x ∈ rest := (List.mem_cons.mp hx).resolve_left (fun hh => hk hh.symm)
      simp only [List.takeWhile_cons, hb, if_true, List.cons_append]
      obtain ⟨u, hu⟩ := ih hx'
      exact ⟨u, by simp [hu]⟩



/-! ## SF5 — composition is `∗`, and SF7 — `Row` is derived

The PCM would be decoration if composing two claims did not mean conjoining what
they assert, and `row` would be decoration if owning it did not *entail the
resolution*. Both below. Together they are why §7's two measured blockers clear
by construction: two `Row`s through one mixin compose (they agree on the shared
`defined` slot and own disjoint `empty` segments), and each still resolves.
-/

/-- Composition is conjunction — both directions, since composition concatenates. -/
theorem holds_compose {a b c : SlotClaim} {h : Heap}
    (hcomp : SlotClaim.compose a b = some c) :
    (c.Holds h ↔ a.Holds h ∧ b.Holds h) := by
  unfold SlotClaim.compose at hcomp
  split at hcomp
  · injection hcomp with hcomp
    subst hcomp
    unfold SlotClaim.Holds
    simp only [List.mem_append]
    constructor
    · rintro ⟨hd, he, hs, hm⟩
      exact ⟨⟨fun x hx => hd x (Or.inl hx), fun x hx => he x (Or.inl hx),
              fun x hx => hs x (Or.inl hx), fun k hk => hm k (Or.inl hk)⟩,
             fun x hx => hd x (Or.inr hx), fun x hx => he x (Or.inr hx),
             fun x hx => hs x (Or.inr hx), fun k hk => hm k (Or.inr hk)⟩
    · rintro ⟨⟨had, hae, has, ham⟩, hbd, hbe, hbs, hbm⟩
      exact ⟨fun x hx => hx.elim (had x) (hbd x), fun x hx => hx.elim (hae x) (hbe x),
             fun x hx => hx.elim (has x) (hbs x), fun k hk => hk.elim (ham k) (hbm k)⟩
  · exact absurd hcomp (by simp)

/-- A walk over all-empty slots finds nothing. -/
theorem lookup_go_none {h : Heap} {m : String} {l : List ObjId}
    (hall : ∀ k ∈ l, slotOf h k m = none) : lookup.go h m l = none := by
  induction l with
  | nil => rfl
  | cons k rest ih =>
    have hk := hall k (by simp)
    unfold lookup.go
    cases hc : h.classPayload? k with
    | none => exact ih fun j hj => hall j (by simp [hj])
    | some c =>
      dsimp only
      cases hf : c.methods.find? (·.1 == m) with
      | none => exact ih fun j hj => hall j (by simp [hj])
      | some e => simp [slotOf, hc, hf] at hk

/-- Nothing before, something here: the walk stops at the owner. -/
theorem lookup_go_hit {h : Heap} {m : String} {before : List ObjId} {owner : ObjId}
    {md : MethodDef} (hb : ∀ k ∈ before, slotOf h k m = none)
    (hown : slotOf h owner m = some md) {rest : List ObjId} :
    lookup.go h m (before ++ owner :: rest) = some (owner, md) := by
  induction before with
  | nil =>
    rw [List.nil_append]
    unfold lookup.go
    cases hc : h.classPayload? owner with
    | none => simp [slotOf, hc] at hown
    | some c =>
      dsimp only
      cases hf : c.methods.find? (·.1 == m) with
      | none => simp [slotOf, hc, hf] at hown
      | some e =>
        have : e.2 = md := by simpa [slotOf, hc, hf] using hown
        simp [this]
  | cons k rest' ih =>
    have hk := hb k (by simp)
    rw [List.cons_append]
    unfold lookup.go
    cases hc : h.classPayload? k with
    | none => exact ih fun j hj => hb j (by simp [hj])
    | some c =>
      dsimp only
      cases hf : c.methods.find? (·.1 == m) with
      | none => exact ih fun j hj => hb j (by simp [hj])
      | some e => simp [slotOf, hc, hf] at hk

/-- **SF7 — owning `row C seg owner m σ` entails the resolution it stands for.**
    The `Row` the type system consumes is not primitive: it is a spine, an `empty`
    segment, a `noMM` segment and one `defined` slot, and *this* is the proof that
    those four add up to "`C` resolves `m` at `owner`". -/
theorem row_lookupIn {h : Heap} {C owner : ObjId} {seg : List ObjId} {m : String}
    {σ : MethodDecl} (hmem : owner ∈ seg)
    (hh : (SlotClaim.row C seg owner m σ).Holds h) :
    ∃ md, lookupIn h C m = some (owner, md) ∧
      md.params.length = σ.params.length ∧ md.undefined = false ∧
      md.visibility = .pub := by
  obtain ⟨hd, he, hs, _⟩ := hh
  obtain ⟨md, hslot, hp, hu, hv⟩ := hd (owner, m, σ) (by simp [SlotClaim.row])
  refine ⟨md, ?_, hp, hu, hv⟩
  have hbefore : ∀ k ∈ seg.takeWhile (· != owner), slotOf h k m = none := by
    intro k hk
    refine he (k, m) ?_
    simp only [SlotClaim.row, List.mem_map]
    exact ⟨k, hk, rfl⟩
  have hspine : seg <+: ancestors h C :=
    List.isPrefixOf_iff_prefix.mp (hs (C, seg) (by simp [SlotClaim.row]))
  have hseg : seg.takeWhile (· != owner) ++ [owner] <+: seg :=
    takeWhile_append_prefix hmem
  obtain ⟨t, ht⟩ := hseg.trans hspine
  unfold lookupIn
  rw [← ht, List.append_assoc, List.cons_append, List.nil_append]
  exact lookup_go_hit hbefore hslot

/-! ## SF-T2 — a whole `SlotClaim` is framed by a non-conflicting write

The rung the design asks for: not "this one resolution survives" but "the
composed footprint survives", with the hypothesis being exactly SF8's decidable
table. Four components, four one-line arguments — which is the payoff of having
made the resources cell-wise in the first place.
-/

/-- The slot the write did not touch is the slot it was. Both halves of SF8's
    first row: a different class (`classPayload?_defineMethod_ne`) or a different
    name (`methods_find_defineMethod`). -/
theorem slotOf_defineMethod_ne {h : Heap} {cls k : ObjId} {name m : String}
    {md : MethodDef} (hne : ¬ (k = cls ∧ m = name)) :
    slotOf (defineMethod h cls name md) k m = slotOf h k m := by
  by_cases hk : k = cls
  · have hm : ¬ (m = name) := fun hh => hne ⟨hk, hh⟩
    have := methods_find_defineMethod h cls k name m md hm
    unfold slotOf
    cases h1 : (defineMethod h cls name md).classPayload? k with
    | none =>
      cases h2 : h.classPayload? k with
      | none => rfl
      | some c => rw [h1, h2] at this; exact absurd this (by simp)
    | some c' =>
      cases h2 : h.classPayload? k with
      | none => rw [h1, h2] at this; exact absurd this (by simp)
      | some c =>
        rw [h1, h2] at this
        simp only [Option.map_some, Option.some.injEq] at this
        simp [this]
  · unfold slotOf; rw [classPayload?_defineMethod_ne h cls k name md hk]

/-- **SF-T2 (the `defineMethod` case).** A claim whose footprint the write misses
    holds after the write. The hypothesis is `Install.conflicts` returning `false`
    — the same `Bool` the validator computes (§5 step 3), no proof term. -/
theorem Holds_defineMethod {c : SlotClaim} {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hc : c.Holds h)
    (hf : (Install.defM cls name).conflicts c = false) :
    c.Holds (defineMethod h cls name md) := by
  obtain ⟨hd, he, hs, hm⟩ := hc
  simp only [Install.conflicts, Bool.or_eq_false_iff, List.any_eq_false,
    Bool.and_eq_false_imp, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨hfd, hfe⟩, hfm⟩ := hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨md', hslot, hp, hu, hv⟩ := hd x hx
    refine ⟨md', ?_, hp, hu, hv⟩
    rw [slotOf_defineMethod_ne (fun hh => by
      have := hfd x hx; simp [hh.1, hh.2] at this), hslot]
  · intro x hx
    have := he x hx
    unfold SlotEmpty at this ⊢
    rw [slotOf_defineMethod_ne (fun hh => by
      have := hfe x hx; simp [hh.1, hh.2] at this)]
    exact this
  · intro x hx
    have := hs x hx
    unfold Spine at this ⊢
    rw [ancestors_defineMethod]; exact this
  · intro k hk
    have := hm k hk
    unfold NoMM at this ⊢
    rw [slotOf_defineMethod_ne (fun hh => by
      obtain ⟨h1, h2⟩ := hh
      subst h1
      exact absurd hk (by simpa using hfm h2.symm))]
    exact this

/-! ## SF-T1 — `ResolvesAt` under a slot-disjoint write -/

/-- **SF-T1.** `ResolvesAt` survives a `def` of the *same* name, provided the
    resolution already completes before the written class — i.e. `cls` is on
    neither the claim's `empty` segment nor its `defined` slot (SF8's first row,
    read contrapositively).

    The hypothesis is stated as data about the walk rather than as membership so
    that it is decidable exactly as written; `resolvesAt_defineMethod_slot` below
    is the membership-shaped corollary a `SlotClaim` supplies. -/
theorem ResolvesAt_defineMethod_frame {h : Heap} {k : ObjId} {mname bid : String}
    {cls : ObjId} {name : String} {md : MethodDef}
    (hr : ResolvesAt h k mname bid)
    (hbef : lookup.go h mname ((ancestors h k).takeWhile (· != cls))
              = lookupIn h k mname) :
    ResolvesAt (defineMethod h cls name md) k mname bid := by
  obtain ⟨owner, md0, hlook, hb, hu, hvis, hpre, hbtw⟩ := hr
  refine ⟨owner, md0, ?_, hb, hu, hvis, hpre, ?_⟩
  · unfold lookupIn at hlook ⊢
    rw [ancestors_defineMethod]
    refine lookup_go_prefix (List.takeWhile_prefix (p := (· != cls))) ?_
    rw [lookup_go_off not_mem_takeWhile_ne, hbef]
    exact hlook
  · rw [ancestors_defineMethod, crubyShadow_defineMethod]; exact hbtw

/-- **The `SlotClaim`-shaped corollary.** `cls` off the segment the claim owns —
    not on the `empty` prefix, and not the `defined` owner — is exactly SF8's
    first row read contrapositively, and it frames the resolution. -/
theorem ResolvesAt_defineMethod_slot {h : Heap} {k owner : ObjId} {mname bid : String}
    {cls : ObjId} {name : String} {md md0 : MethodDef}
    (hr : ResolvesAt h k mname bid)
    (hown : lookupIn h k mname = some (owner, md0))
    (hoff : cls ∉ (ancestors h k).takeWhile (· != owner) ++ [owner]) :
    ResolvesAt (defineMethod h cls name md) k mname bid := by
  have hmem : owner ∈ ancestors h k := lookup_go_mem hown
  have hpre : (ancestors h k).takeWhile (· != owner) ++ [owner] <+: ancestors h k :=
    takeWhile_append_prefix hmem
  refine ResolvesAt_defineMethod_frame hr ?_
  rw [hown]
  refine lookup_go_prefix (prefix_takeWhile_of_not_mem hpre hoff) ?_
  exact lookup_go_of_prefix_mem hpre hown (by simp)

end Static
end Proof
end RubyCore
