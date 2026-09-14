import Denote.Sem.Frame
import Ratchet.Judge
import RubyCore.HeapCert

/-!
# `Denote/Sanity.lean` — the ladder is not vacuous

Every one of the 83 obligations begins `∀ m, StateOk κ Γ I m → …`, so if `StateOk` were
unsatisfiable the whole ladder would be a list of vacuous truths. That was a theoretical
worry while `StateOk` was eleven components read off `Ctx`; it stopped being theoretical when
`Judge.strLit` forced two more that are claims about the *heap* rather than about the
description (`HeapSaturated`, `CoreOk` — clink 45). A hypothesis nobody has exhibited a model
of is a hypothesis that might be false.

So: **`StateOk` at the real prelude-booted machine**, proved, in the empty context. It is the
weakest interesting instance — `ctx0`, no locals, no ivars — and that is the point: it is
exactly the state a whole-program judgment starts in, so the *top-level* reading of every
obligation is non-vacuous.

Both new components are `decide`d rather than assumed, and each is worth a sentence:

* `CoreOk` is four facts about the boot classes, all of them ancestor walks or a constant
  lookup at a 105-object heap.
* `HeapSaturated` goes through the model's own certificate, `RubyCore.saturatedB` +
  `RubyCore.Proof.saturatedB_sound` — the same "a hypothesis the harness can check beats an
  `axiom`" trade that file's header argues for, reused rather than re-argued.

What this does **not** do: it does not exhibit a model of a *non-empty* `Γ`, `κ.classes` or
`κ.asms`. Those are satisfiable for boring reasons (they quantify over their own lists) but
the honest statement of what is checked here is the one above.
-/

set_option autoImplicit false

namespace Ratchet.Denote
open RubyCore

/-- The user-code initial machine — the same one `Ratchet.Semantics.run` executes a rung from,
and the same one `Denote/Examples.lean`'s 31 guards observe. A boot failure falls back to a
machine that fails the checks below loudly rather than passing them vacuously.
Do not reuse the phase-one machine: its `preludeMode` is true and its frames are stale. -/
def bootMachine : Machine :=
  match Semantics.bootedMachine with
  | .ok m => { Machine.initOn m.heap .nil with globals := m.globals }
  | .error _ => Machine.init .nil

#guard !bootMachine.preludeMode

theorem bootMachine_kont : bootMachine.kont = [] := by
  unfold bootMachine
  cases Semantics.bootedMachine <;> rfl

/-- `CoreOk` as a `Bool`, so all its clauses are checked at boot. -/
def coreDataB (h : Heap) : Bool :=
  (ancestors h Boot.basicObjectId == [Boot.basicObjectId]) &&
  (classNamed? h "String" == some Boot.stringId) &&
  (ancestors h Boot.stringId).contains Boot.stringId &&
  (ancestors h Boot.stringId).contains Boot.basicObjectId &&
  (classNamed? h "Regexp" == some Boot.regexpId) &&
  (ancestors h Boot.regexpId).contains Boot.regexpId &&
  (ancestors h Boot.regexpId).contains Boot.basicObjectId &&
  (ancestors h Boot.procId).contains Boot.basicObjectId &&
  (ancestors h Boot.arrayId).contains Boot.basicObjectId &&
  (ancestors h Boot.hashId).contains Boot.basicObjectId &&
  coreClsNames.all (fun n =>
    match constLookup h n with
    | some (.ref o) => (h.classPayload? o).isSome
    | some _ => false
    | none => true)

def coreOkB (h : Heap) : Bool := classReadyB h && coreDataB h

theorem coreOkB_sound {h : Heap} (hb : coreOkB h = true) : CoreOk h := by
  simp only [coreOkB, coreDataB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc] at hb
  rcases hb with ⟨hc, hb, sn, ss, sb, rn, rs, rb, pb, ab, hb', names⟩
  refine ⟨classReadyB_sound hc, hb, sn, ss, sb, rn, rs, rb, pb, ab, hb', ?_⟩
  intro n hn v hv
  have := names n hn
  rw [hv] at this
  cases v with
  | ref o => exact ⟨o, rfl, by simpa using this⟩
  | _ => exact absurd this (by simp)

/-- `self` has no instance variables — a `Bool`, because the toplevel `self` of the booted
machine is a real heap object built by the prelude. -/
def selfIvarsEmptyB (m : Machine) : Bool :=
  match m.currentFrame.self with
  | .ref o => (m.heap.get o).ivars.isEmpty
  | _ => true

/-- … and then every ivar read at `self` is `nil`, which is `SelfSpineOk`'s completeness clause
at the empty spine. -/
theorem selfIvarsEmpty_sound {m : Machine} (h : selfIvarsEmptyB m = true) (x : String) :
    ivarOf m.heap m.currentFrame.self x = .nil := by
  unfold selfIvarsEmptyB at h
  unfold ivarOf
  cases hs : m.currentFrame.self with
  | ref o =>
    rw [hs] at h
    have : (m.heap.get o).ivars = [] := List.isEmpty_iff.mp h
    simp [this]
  | _ => rfl

/-- The **four** frame facts the starting machine has to have: it is not inside a method body,
it was not called with a block, it *has* a current frame (`StateOk.frameInRange`), and `self`
carries no instance variables.

The fourth is new (clink 48) and it is the boot-machine half of `SelfSpineOk`'s completeness
clause: the empty spine `.ivar0` mentions nothing, so completeness at `ctx0` says every ivar
of the toplevel `self` reads as `nil`. Measured rather than assumed, like the other three —
the prelude runs before this machine exists and could have set an ivar on `main`. -/
def frameOkB (m : Machine) : Bool :=
  (m.currentFrame.kind != .method) && m.currentFrame.blk.isNone &&
  !m.stack.isEmpty && (m.stack.headD 0 < m.frames.size) && selfIvarsEmptyB m

/-- **A toplevel frame shadows nothing** — `ConstScopeOk` at the one frame shape that makes it
free. With `cref = [Object]` the lexical phase of `evalExpr`'s `.const` arm is a single
`constOwn` at `Object`, which *is* `constLookup`, so it hits and the inheritance phase never
runs. That is the fifth `frameOkB` clause, and it is decidable for the same reason the other
four are. -/
theorem constOwn_object (h : Heap) (n : String) :
    constOwn h Boot.objectId n = constLookup h n := by
  simp only [constOwn, constLookup]
  cases h.classPayload? Boot.objectId <;> rfl

/-- A `firstM` over `Option` whose every probe misses, misses. -/
theorem firstM_none : ∀ (l : List ObjId) (f : ObjId → Option Value),
    (∀ a ∈ l, f a = none) → l.firstM f = none
  | [], _, _ => rfl
  | a :: l, f, h => by
    have ha : f a = none := h a (by simp)
    have hl : l.firstM f = none := firstM_none l f (fun b hb => h b (by simp [hb]))
    simp [List.firstM, ha, hl]

/-- **The three frame facts that make constant resolution toplevel resolution**: the lexical
scope is `[Object]`, the definee is `Object`, and every *other* ancestor of `Object` owns no
constants.

The third is the one that is not obvious and is the reason this is not a one-liner.
`constLookupFrom` — the inheritance phase — walks `ancestors h Object`, which is
`[Object, Kernel, BasicObject]`, so it can answer where `constLookup` (which reads `Object`'s
own table and stops) answers `none`. Measured at the booted heap: `Kernel` and `BasicObject`
own zero constants, so the two agree. Decidable, and checked by `bootOkB` below. -/
def topScopeB (m : Machine) : Bool :=
  (m.currentFrame.cref == [Boot.objectId]) && (m.currentFrame.defmod == Boot.objectId) &&
  (ancestors m.heap Boot.objectId).all (fun k =>
    (k == Boot.objectId) ||
      (match m.heap.classPayload? k with | some c => c.consts.isEmpty | none => true))

theorem constScope_of_topScope {m : Machine} (hb : topScopeB m = true) : ConstScopeOk m := by
  simp only [topScopeB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hb
  obtain ⟨⟨hcref, hdefmod⟩, hanc⟩ := hb
  intro n
  simp only [constResolveAt, hcref, hdefmod, List.firstM, constOwn_object]
  cases hl : constLookup m.heap n with
  | some w => simp
  | none =>
    have hfrom : constLookupFrom m.heap Boot.objectId n = none := by
      refine firstM_none _ _ (fun k hk => ?_)
      have := hanc k (by simpa using hk)
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with hk0 | hempty
      · subst hk0; exact hl
      · cases hp : m.heap.classPayload? k with
        | none => simp
        | some c =>
          rw [hp] at hempty
          have : c.consts = [] := List.isEmpty_iff.mp (by simpa using hempty)
          simp [this]
    simp [hfrom]
    rfl

/-- **"And nothing more", as one `Bool`.** Every method installed anywhere in the heap is a
builtin, a prelude definition, or a name `κ` records.

Only ids below `objs.size` are scanned, and that is complete rather than a shortcut:
`Heap.get` is total and answers `default` past the end, whose payload is `.none`, so
`classPayload?` at a dangling id is `none` and there is nothing there to check
(`Denote/Ext.lean`'s `get_oob` is the same fact the allocating rungs spend). -/
def methodsExactB (κ : Ratchet.Ctx) (m : Machine) : Bool :=
  (List.range m.heap.objs.size).all fun k =>
    match m.heap.classPayload? k with
    | some cp => cp.methods.all fun p =>
        p.2.fromPrelude || p.2.builtin.isSome || !nameFreeN κ p.1
    | none => true

theorem classPayload?_oob (h : Heap) {o : ObjId} (ho : h.objs.size ≤ o) :
    h.classPayload? o = none := by
  simp only [Heap.classPayload?, get_oob h ho]; rfl

theorem methodsExactB_sound {κ : Ratchet.Ctx} {m : Machine} (hb : methodsExactB κ m = true) :
    MethodsExact κ m := by
  intro k cp hk n md hmem
  by_cases hlt : k < m.heap.objs.size
  · simp only [methodsExactB, List.all_eq_true] at hb
    have hall := hb k (by simpa using hlt)
    rw [hk] at hall
    simp only [List.all_eq_true, Bool.or_eq_true] at hall
    rcases hall (n, md) (by simpa using hmem) with (h3 | h3) | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (by simpa using h3))
  · rw [classPayload?_oob m.heap (Nat.le_of_not_lt hlt)] at hk
    exact absurd hk (by simp)

/-- Check actual absence at all relevant sites. This is stronger than `NameFreeOk`'s
builtin/tombstone disjunction and also discharges `BareNameFree` at current self. -/
def nameFreeB (m : Machine) : Bool :=
  shadowableNames.all fun n => (nameFreeSites m).all fun k =>
    (Interp.methodOn m.heap k n).isNone

def selfLiveB (m : Machine) : Bool :=
  match m.currentFrame.self with
  | .ref o => o < m.heap.objs.size
  | _ => true

theorem nameFreeB_sound {m : Machine} (hb : nameFreeB m = true) (κ : Ratchet.Ctx) :
    NameFreeOk κ m := by
  intro n hn k hk o md hm
  simp only [nameFreeB, List.all_eq_true] at hb
  have := hb n hn k hk
  rw [hm] at this
  exact absurd this (by simp)

/-- **A class the heap does not hold has no methods.** `ancestors` at an id with no class
payload is `[id]`, and `methodOn` then reads that same absent payload — so the walk answers
`none` without the id needing to be in range. This is what lets `queryOkB` check a *bounded*
range and still discharge a component quantified over every id. -/
theorem methodOn_of_no_payload {h : Heap} {k : ObjId} (hp : h.classPayload? k = none)
    (n : String) : Interp.methodOn h k n = none := by
  -- the walk at an id with no payload is `[id]`, and `firstM` over it reads that same
  -- absent payload
  show List.firstM _ (RubyCore.ancestors h k) = none
  have hanc : RubyCore.ancestors h k = [k] := by
    simp only [RubyCore.ancestors, RubyCore.ancestors.go, hp]
    rfl
  rw [hanc]
  simp only [List.firstM, hp]
  rfl

theorem classPayload?_out_of_range {h : Heap} {k : ObjId} (hk : ¬ k < h.objs.size) :
    h.classPayload? k = none := by
  simp only [Heap.classPayload?, Heap.get]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using hk)]
  rfl

/-- **`QueryOk` as one `Bool`** (clink 54): the five things `invokeDispatch` tests before it
runs a builtin, plus the miss clause, at every class the heap holds. The two lemmas above cover
everything outside the range. -/
def queryOkB (m : Machine) : Bool :=
  (List.range m.heap.objs.size).all (fun k =>
    Ratchet.Denote.queryBuiltins.all (fun p =>
      match Interp.methodOn m.heap k p.1 with
      | none =>
        match Interp.methodOn m.heap k "method_missing" with
        | none => true
        | some (_, mm) => mm.builtin.isSome
      | some (owner, md) =>
        md.builtin == some p.2 && !md.undefined && md.visibility == Visibility.pub
          && !md.fromPrelude
          && (Interp.crubyShadow m.heap
                ((RubyCore.ancestors m.heap k).takeWhile (fun x => x != owner)) p.1).isNone))

/-- The class-query rows at one dispatch site. -/
def clsQueryAtB (m : Machine) (k : ObjId) : Bool :=
    Ratchet.Denote.clsQueryBuiltins.all (fun p =>
      match Interp.methodOn m.heap k p.1 with
      | none =>
        match Interp.methodOn m.heap k "method_missing" with
        | none => true
        | some (_, mm) => mm.builtin.isSome
      | some (owner, md) =>
        md.builtin == some p.2 && !md.undefined && md.visibility == Visibility.pub
          && !md.fromPrelude
          && (Interp.crubyShadow m.heap
                ((RubyCore.ancestors m.heap k).takeWhile
                  (fun x => x != owner)) p.1).isNone)

/-- Check existing class receivers and the direct Class path used by fresh eigenclasses. -/
def clsQueryOkB (m : Machine) : Bool :=
  clsQueryAtB m Boot.classId && (List.range m.heap.objs.size).all (fun o =>
    !(m.heap.classPayload? o).isSome || clsQueryAtB m (classOf m.heap (.ref o)))

/-- **`BaseChainsOk` as one `Bool`.** Three computations per row: every name in the row
resolves to an ancestor of the base, every *constant* name that resolves into the base's
ancestors is in the row, and no class id descends from the base but itself.

The second is where the boot constant table is swept rather than the string space: a name
`classNamed?` answers for is necessarily one the table carries, which is what makes the finite
check the whole claim. -/
def baseChainsOkB (m : Machine) : Bool :=
  let names : List String :=
    match m.heap.classPayload? Boot.objectId with
    | some c => c.consts.map (fun (q : String × Value) => q.1)
    | none => []
  Ratchet.Denote.builtinBases.all (fun p =>
    (match p.2.head? with
     | some bn => classNamed? m.heap bn == some p.1
     | none => false) &&
    p.2.all (fun cn =>
      match classNamed? m.heap cn with
      | some j => (RubyCore.ancestors m.heap p.1).contains j
      | none => false) &&
    names.all (fun cn =>
      match classNamed? m.heap cn with
      | some j => !(RubyCore.ancestors m.heap p.1).contains j || p.2.contains cn
      | none => true) &&
    (List.range m.heap.objs.size).all (fun k =>
      !(RubyCore.ancestors m.heap k).contains p.1 || k == p.1))

/-- A name `classNamed?` answers for is one the boot constant table carries. Extracted because
`baseChainsOkB`'s middle clause sweeps that table and the soundness step is exactly this. -/
theorem classNamed?_mem_consts {m : Machine} {cn : String} {j : ObjId}
    (h : classNamed? m.heap cn = some j) :
    cn ∈ (match m.heap.classPayload? Boot.objectId with
          | some c => c.consts.map (fun (q : String × Value) => q.1)
          | none => ([] : List String)) := by
  -- `classNamed?` resolves through `constLookup`, which is a `find?` in `Object`'s own
  -- constant table — so the name it answered for is one that table carries
  simp only [classNamed?] at h
  cases hcl : constLookup m.heap cn with
  | none => rw [hcl] at h; exact absurd h (by simp)
  | some w =>
    simp only [constLookup] at hcl
    cases hp : m.heap.classPayload? Boot.objectId with
    | none => rw [hp] at hcl; exact absurd hcl (by simp)
    | some c =>
      rw [hp] at hcl
      simp only [hp]
      dsimp only at hcl
      cases hf : List.find? (fun x => x.fst == cn) c.consts with
      | none => rw [hf] at hcl; exact absurd hcl (by simp)
      | some q =>
        have hq : q.1 = cn := by simpa using List.find?_some hf
        exact hq ▸ List.mem_map_of_mem (List.mem_of_find?_eq_some hf)
        

/-- Ancestors of an id with no class payload: itself. So the subclass sweep over the *live*
ids is the whole claim — an id past the end of the heap has `[k]`, which contains the base only
when it *is* the base. -/
theorem ancestors_of_not_class {h : Heap} {k : ObjId} (hp : h.classPayload? k = none) :
    RubyCore.ancestors h k = [k] := by
  simp only [RubyCore.ancestors, RubyCore.ancestors.go, hp]
  rfl

theorem baseChainsOkB_sound {m : Machine} (hb : baseChainsOkB m = true) (κ : Ratchet.Ctx) :
    Ratchet.Denote.BaseChainsOk κ m := by
  intro base ch hmem
  simp only [baseChainsOkB, List.all_eq_true] at hb
  have hrow := hb (base, ch) (by simpa using hmem)
  simp only [Bool.and_eq_true, List.all_eq_true] at hrow
  obtain ⟨⟨⟨hhd, hin⟩, hout⟩, hsub⟩ := hrow
  refine ⟨fun _ => ⟨fun bn hbn => ?_, fun cn hcn => ?_⟩,
    fun _ => ⟨fun cn j _ hj hanc => ?_, fun k hk => ?_⟩⟩
  · rw [hbn] at hhd; simpa using hhd
  · have := hin cn (by simpa using hcn)
    cases hcnm : classNamed? m.heap cn with
    | none => rw [hcnm] at this; exact absurd this (by simp)
    | some j => exact ⟨j, rfl, by rw [hcnm] at this; simpa using this⟩
  · have := hout cn (by simpa using classNamed?_mem_consts hj)
    rw [hj] at this
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h' | h'
    · exact absurd hanc (by rw [h']; simp)
    · simpa using h'
  · by_cases hlt : k < m.heap.objs.size
    · have := hsub k (by simpa using hlt)
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
      rcases this with h' | h'
      · exact absurd hk (by rw [h']; simp)
      · exact h'
    · -- past the end of the heap: `ancestors` is `[k]`
      rw [ancestors_of_not_class (classPayload?_out_of_range hlt)] at hk
      exact (by simpa using hk : base = k).symm

theorem clsQueryOkB_sound {m : Machine} (hb : clsQueryOkB m = true) (κ : Ratchet.Ctx) :
    Ratchet.Denote.ClsQueryOk κ m := by
  intro mname bid hmem _ k hp
  simp only [clsQueryOkB, Bool.and_eq_true] at hb
  obtain ⟨hclass, hobjects⟩ := hb
  have hrow : clsQueryAtB m k = true := by
    rcases hp with hk | ⟨o, ho, hco⟩
    · subst k; exact hclass
    · have hlt := Ratchet.Denote.lt_size_of_classPayload ho
      have hr := List.all_eq_true.mp hobjects o (by simpa using hlt)
      simpa only [ho, Bool.not_true, Bool.false_or, hco] using hr
  have hp2 := List.all_eq_true.mp hrow (mname, bid) (by simpa using hmem)
  refine ⟨?_, ?_⟩
  · intro owner md hfound
    rw [hfound] at hp2
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp2
    obtain ⟨⟨⟨⟨hb1, hu⟩, hv⟩, hpre⟩, hsh⟩ := hp2
    exact ⟨hb1, by simpa using hu, by simpa using hv, by simpa using hpre, by simpa using hsh⟩
  · intro hnone o₂ md hfound
    rw [hnone, hfound] at hp2
    exact hp2

/-- **`NilQueryOk` as one `Bool`** — the same five facts, with the bid a *disjunction* of the
two `nil?` implementations. -/
def nilQueryOkB (m : Machine) : Bool :=
  (List.range m.heap.objs.size).all (fun k =>
    match Interp.methodOn m.heap k "nil?" with
    | none =>
      match Interp.methodOn m.heap k "method_missing" with
      | none => true
      | some (_, mm) => mm.builtin.isSome
    | some (owner, md) =>
      (md.builtin == some "Object#nil?" || md.builtin == some "NilClass#nil?")
        && !md.undefined && md.visibility == Visibility.pub && !md.fromPrelude
        && (Interp.crubyShadow m.heap
              ((RubyCore.ancestors m.heap k).takeWhile (fun x => x != owner)) "nil?").isNone)

theorem nilQueryOkB_sound {m : Machine} (hb : nilQueryOkB m = true) (κ : Ratchet.Ctx) :
    Ratchet.Denote.NilQueryOk κ m := by
  intro _ k
  by_cases hk : k < m.heap.objs.size
  · have hrow := List.all_eq_true.mp hb k (by simpa using hk)
    refine ⟨?_, ?_⟩
    · intro owner md hfound
      rw [hfound] at hrow
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hrow
      obtain ⟨⟨⟨⟨hb1, hu⟩, hv⟩, hp⟩, hsh⟩ := hrow
      exact ⟨hb1, by simpa using hu, by simpa using hv, by simpa using hp,
             by simpa using hsh⟩
    · intro hnone o md hfound
      rw [hnone, hfound] at hrow
      exact hrow
  · exact ⟨by
      intro owner md hfound
      rw [methodOn_of_no_payload (classPayload?_out_of_range hk)] at hfound
      exact absurd hfound (by simp), by
      intro _ o md hfound
      rw [methodOn_of_no_payload (classPayload?_out_of_range hk)] at hfound
      exact absurd hfound (by simp)⟩

theorem queryOkB_sound {m : Machine} (hb : queryOkB m = true) (κ : Ratchet.Ctx) :
    Ratchet.Denote.QueryOk κ m := by
  intro mname bid hmem _ k
  by_cases hk : k < m.heap.objs.size
  · have hrow := List.all_eq_true.mp (List.all_eq_true.mp hb k (by simpa using hk))
      (mname, bid) (by simpa using hmem)
    refine ⟨?_, ?_⟩
    · intro owner md hfound
      rw [hfound] at hrow
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hrow
      obtain ⟨⟨⟨⟨hb1, hu⟩, hv⟩, hp⟩, hsh⟩ := hrow
      exact ⟨hb1, by simpa using hu, by simpa using hv, by simpa using hp,
             by simpa using hsh⟩
    · intro hnone o md hfound
      rw [hnone, hfound] at hrow
      exact hrow
  · exact ⟨by
      intro owner md hfound
      rw [methodOn_of_no_payload (classPayload?_out_of_range hk)] at hfound
      exact absurd hfound (by simp), by
      intro _ o md hfound
      rw [methodOn_of_no_payload (classPayload?_out_of_range hk)] at hfound
      exact absurd hfound (by simp)⟩

/-- **`MissFree` as one `Bool`.** One walk, one field. Checked in the form the component
states — `none`, or a `builtin` behind it — rather than in the stronger "absent" form, because
here the two are *not* interchangeable: the model's `method_missing` really may be a builtin
(`BasicObject#method_missing`), and a check that demanded absence would fail at the booted
machine and cost the ladder its only exhibited model. -/
def missFreeB (m : Machine) : Bool :=
  match Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) "method_missing" with
  | none => true
  | some (_, md) => md.builtin.isSome

theorem missFreeB_sound {m : Machine} (hb : missFreeB m = true) (κ : Ratchet.Ctx) :
    MissFree κ m := by
  intro _ _ o md hm
  unfold missFreeB at hb
  rw [hm] at hb
  exact hb

/-- **`BareNameFree` from `nameFreeB`.** `nameFreeB` already checks the strongest form of
`NameFreeOk` — nothing on the chain carries the name at all — and `"x"` is one of the three
names it checks, so the same `Bool` discharges this component too. That is not a coincidence
worth hiding: `BareNameFree` is `NameFreeOk` at one name with the two escapes the interpreter
does not honour removed, so any measurement strong enough for the first covers it.

The `BareNameError` inversion is what keeps the name list from being duplicated: the table has
one row, and if it grows this proof stops compiling until `shadowableNames` grows with it. -/
theorem bareNameFreeB_sound {m : Machine} (hb : nameFreeB m = true) (κ : Ratchet.Ctx) :
    BareNameFree κ m := by
  intro n hn _ _
  cases hn
  simp only [nameFreeB, List.all_eq_true] at hb
  have h := hb "x" (by simp [shadowableNames]) (classOf m.heap m.currentFrame.self)
    (by simp [nameFreeSites])
  rw [lookup_eq_methodOn]
  simpa using h

theorem selfLiveB_sound {m : Machine} (hb : selfLiveB m = true) : SelfLive m := by
  intro o ho
  unfold selfLiveB at hb
  rw [ho] at hb
  simpa using hb

/-- The current frame binds nothing and captures nothing, so `getLocal` answers `nil` at every
name — which is `EnvOk`'s completeness clause (clink 55) at the empty environment. A `Bool`
rather than a proof for the file's usual reason: `bootMachine` is the *booted* machine, not a
literal, so its frame's locals are not syntactically available. -/
def localsEmptyB (m : Machine) : Bool :=
  (m.frames[m.stack.head?.getD 0]?.getD default).locals.isEmpty &&
    (m.frames[m.stack.head?.getD 0]?.getD default).captured.isNone

theorem localsEmptyB_sound {m : Machine} (h : localsEmptyB m = true) (x : String) :
    m.getLocal x = .nil := by
  simp only [localsEmptyB, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at h
  obtain ⟨hl, hc⟩ := h
  simp [Machine.getLocal, Machine.getLocal.go, hl, hc]

/-- **Everything about the booted machine that has to be computed rather than proved.**

One `Bool`, checked by the `#guard` below — which is the same status
`Denote/Examples.lean`'s 31 guards have, and the same trade
`RubyCore/Proof/AncestorsGrow.lean` makes for `saturatedB`: a hypothesis the build checks
beats an `axiom`, and beats a proof nobody has finished.

It cannot be a `decide`, and the reason is worth stating rather than discovering: the booted
heap is the output of `Interp.run 200_000` over the whole prelude
(`RubyCore/PreludeBoot.lean`), so kernel reduction of it is not on the table. The alternative
that *is* a proof — `native_decide` — buys a theorem at the price of `Lean.ofReduceBool`, and
this package's rule is that every file reports only `propext`/`Classical.choice`/`Quot.sound`.
So the witness below is stated **conditionally on this `Bool`**, and the `Bool` is a build
gate. -/
def bootOkB : Bool :=
  saturatedB bootMachine.heap && coreOkB bootMachine.heap && frameOkB bootMachine &&
  topScopeB bootMachine && methodsExactB Ratchet.ctx0 bootMachine &&
  nameFreeB bootMachine && missFreeB bootMachine && selfLiveB bootMachine &&
  localsEmptyB bootMachine && queryOkB bootMachine && clsQueryOkB bootMachine
    && baseChainsOkB bootMachine && nilQueryOkB bootMachine
    && primitiveDispatchB bootMachine.heap (nameFreeN Ratchet.ctx0)
    && primitiveErrorsB bootMachine.heap && stringPayloadB bootMachine.heap
    && arrayPayloadB bootMachine.heap
    && hashPayloadB bootMachine.heap && mainReadyB bootMachine

/-- **The satisfiability witness.** `StateOk` holds at the real booted machine in the empty
context, so no obligation on the ladder is vacuously true for want of a conformant machine.

The hypothesis is discharged by the `#guard` below, at build time, against the same
prelude-booted heap the difftest SUT and `Denote/Examples.lean` use. -/
theorem stateOk_boot (hb : bootOkB = true) : StateOk Ratchet.ctx0 [] .ivar0 bootMachine := by
  simp only [bootOkB, Bool.and_eq_true] at hb
  obtain ⟨hb, hready⟩ := hb
  obtain ⟨⟨⟨⟨⟨hb, hpd⟩, hpe⟩, hsp⟩, hap⟩, hhp⟩ := hb
  simp only [frameOkB, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none,
    decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsat, hcore⟩, ⟨⟨⟨hkind, hblk⟩, hne⟩, hfr⟩, hself⟩, htop⟩, hex⟩, hnf⟩, hmf⟩,
    hsl⟩, hle⟩, hq⟩, hcq⟩, hbc⟩, hnq⟩ := hb
  exact
    { runtime := fun _ => mainReadyB_sound hready
      classRuntime := by intro cn h; cases h
      primitiveDispatch := hpd
      primitiveErrors := hpe
      stringPayload := stringPayloadB_sound hsp
      arrayPayload := arrayPayloadB_sound hap
      hashPayload := hashPayloadB_sound hhp
      sat := Proof.saturatedB_sound hsat
      core := coreOkB_sound hcore
      env := ⟨by intro x τ hx; exact absurd hx (by simp [envGet?, Ratchet.ctx0]),
              -- completeness at the boot machine: the toplevel frame binds nothing, so every
              -- name reads as `nil`
              fun x _ => localsEmptyB_sound hle x⟩
      selfSpine := ⟨by simp [denSpine, denSpineFrom], fun x _ _ => selfIvarsEmpty_sound hself x⟩
      constPaths := by
        intro owner n τ k hk _ _ _
        exact absurd hk (by simp [envGet?, List.find?, Ratchet.ctx0])
      nested := by
        intro owner n c hc _ _ _ _
        exact absurd hc (by simp [Ratchet.clsGet?, Ratchet.ctx0, Ratchet.Ctx.classes])
      query := queryOkB_sound hq Ratchet.ctx0
      clsQuery := clsQueryOkB_sound hcq Ratchet.ctx0
      baseChains := baseChainsOkB_sound hbc Ratchet.ctx0
      nilQuery := nilQueryOkB_sound hnq Ratchet.ctx0
      -- vacuous at `ctx0`: the class table is empty, exactly as for `ClassesOk`/`DefsOk`
      declCls := by intro c hc; exact absurd hc (by simp [Ratchet.ctx0, Ratchet.Ctx.classes])
      classes := by intro c hc; exact absurd hc (by simp [Ratchet.ctx0, Ratchet.Ctx.classes])
      defs := by intro d hd; exact absurd hd (by simp [Ratchet.ctx0, Ratchet.Ctx.defs])
      asms := by intro a ha; exact absurd ha (by simp [Ratchet.ctx0, Ratchet.Ctx.asms])
      frameInRange := ⟨by simpa using hne, hfr⟩
      frame := by simp only [FrameOk, Ratchet.ctx0]; exact hkind
      closures := trivial
      blockTy := by simp only [BlockTyOk, Ratchet.ctx0]; exact hblk
      selfTy := by simp [SelfTyOk, Ratchet.ctx0]
      consts := by
        intro p τ hp
        exact absurd hp (by simp [constGet?, Ratchet.constPaths, envGet?, Ratchet.ctx0,
          Ratchet.Ctx.consts, Ratchet.Ctx.frame])
      privConsts := trivial
      constScope := constScope_of_topScope htop
      exact := methodsExactB_sound hex
      nameFree := nameFreeB_sound hnf _
      bareFree := bareNameFreeB_sound hnf _
      missFree := missFreeB_sound hmf _
      selfLive := selfLiveB_sound hsl }

-- **The gate.** If this fails, the ladder's hypothesis has no exhibited model and every
-- rung on it is suspect.
#guard bootOkB

#print axioms stateOk_boot

end Ratchet.Denote
