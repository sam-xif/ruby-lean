import Denote.Sem.NarrowState
import Denote.Join

/-!
# `Denote/Sem/Mut.lean` — the transport for an **instance-variable write**

`Ext` is the transport for an *allocation*: the heap only grew and every old object reads back
identically. That is what `denM`'s `.inst` and `clos` arms need, and it is why `Ext` pins
`Heap.get`.

An ivar write is not an `Ext`. It is the first machine change on this ladder that **mutates an
existing object**, and it needs its own relation, because exactly one thing about the heap
moved: some objects' `ivars` lists. Everything else — the size, and every object's class,
eigenclass, payload and frozen bit — is where it was, and that is what the twenty
heap-shaped components of `StateOk` actually read.

## Why it is a separate relation rather than a weaker `Ext`

`Ext` cannot be weakened to cover this: `denM_ext`'s `.inst` arm reads `ivarOf`, and its `clos`
arm reads the captured frame's locals, so both need `get` in full. The two relations divide the
work the way the components divide: `Mut` transports everything that reads the heap's *shape*,
and the two components that read an object's *contents* — `EnvOk` and `SelfSpineOk` — are
handled at the rung, where the assignment's own guard (`found-issues.md` §F17's
`ivarStaleFree`) is available.

So this file is deliberately **not** a `StateOk_mut`: it is `MutOk`, the eighteen components
that travel, and the rung composes it with the two that do not.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **The heap changed only in some objects' instance variables.** -/
structure Mut (m m₂ : Machine) : Prop where
  frames : m₂.frames = m.frames
  stack : m₂.stack = m.stack
  globals : m₂.globals = m.globals
  size : m₂.heap.objs.size = m.heap.objs.size
  klass : ∀ o, (m₂.heap.get o).klass = (m.heap.get o).klass
  eigen : ∀ o, (m₂.heap.get o).eigen = (m.heap.get o).eigen
  payloadObj : ∀ o, (m₂.heap.get o).payload = (m.heap.get o).payload
  frozen : ∀ o, (m₂.heap.get o).frozen = (m.heap.get o).frozen

theorem Mut.refl (m : Machine) : Mut m m where
  frames := rfl
  stack := rfl
  globals := rfl
  size := rfl
  klass _ := rfl
  eigen _ := rfl
  payloadObj _ := rfl
  frozen _ := rfl

/-! ## The derived heap facts

Everything `StateOk`'s heap-shaped components read, shown to agree — so each component's
transport below is a rewrite rather than an argument. -/

theorem Mut.classPayload {m m₂ : Machine} (h : Mut m m₂) (k : ObjId) :
    m₂.heap.classPayload? k = m.heap.classPayload? k := by
  simp only [Heap.classPayload?, h.payloadObj k]

theorem Mut.shapeAgree {m m₂ : Machine} (h : Mut m m₂) : RubyCore.Proof.ShapeAgree m.heap m₂.heap :=
  fun k => by rw [h.classPayload k]

theorem Mut.ancestors {m m₂ : Machine} (h : Mut m m₂) (hsat : RubyCore.Proof.Saturated m.heap) (k : ObjId) :
    RubyCore.ancestors m₂.heap k = RubyCore.ancestors m.heap k :=
  (RubyCore.Proof.ancestors_congr_grow h.shapeAgree (by rw [h.size]; exact Nat.le_refl _)
    hsat k).symm ▸ rfl

theorem Mut.classOf {m m₂ : Machine} (h : Mut m m₂) (v : Value) :
    RubyCore.classOf m₂.heap v = RubyCore.classOf m.heap v := by
  cases v with
  | ref o => simp only [RubyCore.classOf, h.eigen o, h.klass o]
  | int _ | flt _ | sym _ | nil => rfl
  | bool b => cases b <;> rfl

theorem Mut.realClassOf {m m₂ : Machine} (h : Mut m m₂) (v : Value) :
    RubyCore.realClassOf m₂.heap v = RubyCore.realClassOf m.heap v := by
  cases v with
  | ref o => simp only [RubyCore.realClassOf, h.klass o]
  | int _ | flt _ | sym _ | nil => rfl
  | bool b => cases b <;> rfl

theorem Mut.constLookupEq {m m₂ : Machine} (h : Mut m m₂) (n : String) :
    constLookup m₂.heap n = constLookup m.heap n := by
  simp only [constLookup, h.classPayload Boot.objectId]

theorem Mut.classNamedEq {m m₂ : Machine} (h : Mut m m₂) (n : String) :
    classNamed? m₂.heap n = classNamed? m.heap n := by
  simp only [classNamed?]
  rw [h.constLookupEq n]
  cases constLookup m.heap n with
  | none => rfl
  | some w => cases w <;> simp only [h.classPayload]

theorem Mut.methodOn {m m₂ : Machine} (h : Mut m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (k : ObjId) (n : String) :
    Interp.methodOn m₂.heap k n = Interp.methodOn m.heap k n := by
  unfold Interp.methodOn
  rw [h.ancestors hsat k]
  simp only [h.classPayload]

theorem Mut.isA {m m₂ : Machine} (h : Mut m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (v : Value) (k : ObjId) : RubyCore.isA m₂.heap v k = RubyCore.isA m.heap v k := by
  unfold RubyCore.isA
  rw [h.classOf v, h.ancestors hsat]

theorem Mut.isANameEq {m m₂ : Machine} (h : Mut m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (v : Value) (n : String) : isAName m₂.heap v n = isAName m.heap v n := by
  unfold isAName
  rw [h.classNamedEq n]
  cases classNamed? m.heap n with
  | none => rfl
  | some k => exact h.isA hsat v k

theorem Mut.isExactInstEq {m m₂ : Machine} (h : Mut m m₂) (v : Value) (n : String) :
    isExactInst m₂.heap v n = isExactInst m.heap v n := by
  unfold isExactInst
  rw [h.classNamedEq n]
  cases classNamed? m.heap n with
  | none => rfl
  | some k => cases v <;> simp only [h.klass, h.eigen, h.size]

theorem Mut.isClassRefNamedEq {m m₂ : Machine} (h : Mut m m₂) (v : Value) (n : String) :
    isClassRefNamed m₂.heap v n = isClassRefNamed m.heap v n := by
  simp only [isClassRefNamed]
  rw [h.classNamedEq n]

theorem Mut.currentFrame {m m₂ : Machine} (h : Mut m m₂) :
    m₂.currentFrame = m.currentFrame := by
  unfold Machine.currentFrame
  rw [h.stack, h.frames]

theorem Mut.getLocal_go {m m₂ : Machine} (h : Mut m m₂) (x : String) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.getLocal.go m₂ x fid fuel = Machine.getLocal.go m x fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [Machine.getLocal.go, h.frames]
    split
    · rfl
    · split
      · exact ih _
      · rfl

theorem Mut.getLocal {m m₂ : Machine} (h : Mut m m₂) (x : String) :
    m₂.getLocal x = m.getLocal x := by
  simp only [Machine.getLocal, h.stack, h.frames]
  exact h.getLocal_go x _ _

#print axioms Mut.refl
#print axioms Mut.methodOn
#print axioms Mut.isExactInstEq



theorem Mut.arrElems {m m₂ : Machine} (h : Mut m m₂) (v : Value) :
    arrElems? m₂.heap v = arrElems? m.heap v := by
  cases v with
  | ref o => simp only [arrElems?, h.payloadObj o]
  | _ => rfl

theorem Mut.hshEntries {m m₂ : Machine} (h : Mut m m₂) (v : Value) :
    hshEntries? m₂.heap v = hshEntries? m.heap v := by
  cases v with
  | ref o => simp only [hshEntries?, h.payloadObj o]
  | _ => rfl

theorem Mut.procClosure {m m₂ : Machine} (h : Mut m m₂) (v : Value) :
    procClosure? m₂.heap v = procClosure? m.heap v := by
  cases v with
  | ref o => simp only [procClosure?, h.payloadObj o]
  | _ => rfl

theorem Mut.isProcVEq {m m₂ : Machine} (h : Mut m m₂) (v : Value) :
    isProcV m₂.heap v = isProcV m.heap v := by
  unfold isProcV
  rw [h.procClosure v]

/-- A closure's captured-scope reader is a `frames` reader, and `frames` is pinned. -/
theorem Mut.closLocalEq {m m₂ : Machine} (h : Mut m m₂) (cl : Closure) :
    closLocal m₂ cl = closLocal m cl := by
  funext y
  simp only [closLocal, frameLocal, h.frames]
  -- `frameLocal.go` is a fixed walk over `m.frames`, so the two walks are the same walk
  suffices hgo : ∀ (fuel : Nat) (fid : FrameId),
      frameLocal.go m₂ y fid fuel = frameLocal.go m y fid fuel by
    exact hgo _ _
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [frameLocal.go, h.frames]
    split
    · rfl
    · split
      · exact ih _
      · rfl

theorem Mut.closSelfEq {m m₂ : Machine} (h : Mut m m₂) (cl : Closure) :
    closSelf m₂ cl = closSelf m cl := by
  simp only [closSelf, h.frames]

/-- `Mut` is a `Framed`: the stack is pinned and a class stays a class. -/
theorem Mut.framed {m m₂ : Machine} (h : Mut m m₂) : Framed m m₂ :=
  ⟨h.stack, fun k hk => by rw [h.classPayload k]; exact hk⟩

/-! ## The write itself, and the `denM` transport

`Mut` says the heap's *shape* is unmoved. An instance-variable write says more: exactly one
object's `ivars` changed, and exactly at one name. Both halves are needed — the first to
transport the nineteen shape-shaped components, the second to transport `denM` at a type whose
spine mentions that name. -/

/-- **`@x = v` on `selfV`.** Stated as what the *readers* see rather than as `bindIvar`'s
record update, so the rung can discharge it from the step lemma and everything above can be
proved without unfolding `Heap.set`. -/
structure IvarWrite (x : String) (v selfV : Value) (m m₂ : Machine) : Prop extends Mut m m₂ where
  /-- `selfV`'s own ivars: `x` now reads `v`, the rest are where they were. -/
  self : ∀ y, ivarOf m₂.heap selfV y = if y = x then v else ivarOf m.heap selfV y
  /-- Every other value's ivars are untouched. -/
  other : ∀ w, w ≠ selfV → ∀ y, ivarOf m₂.heap w y = ivarOf m.heap w y

theorem IvarWrite.later {x : String} {v selfV : Value} {m m₂ : Machine}
    (h : IvarWrite x v selfV m m₂) (hsat : RubyCore.Proof.Saturated m.heap) :
    Later m m₂ where
  stack := h.stack
  frameCount := by rw [h.frames]
  size := by rw [h.size]; exact Nat.le_refl _
  klass := fun o _ => h.klass o
  eigen := fun o _ => h.eigen o
  payloadObj := fun o _ => h.payloadObj o
  frozen := fun o _ => h.frozen o
  payload := h.classPayload
  -- the ancestor walk needs saturation, which is a `StateOk` component the rung spends here
  ancestors := fun k => h.ancestors hsat k


/-- **`denM` survives an instance-variable write, at a type that agrees about the name.**
The heart of the transport, and the one place `ivarAgree` (`Ratchet/Judge.lean`, §F17) is
*spent* rather than threaded.

Stated as a **conjunction** — the value reading and the spine walk — because the two recur
into each other: `.inst`'s second half and `.clos`'s captured scope are spine walks whose
entries are types, and a spine entry's type may itself be an `.inst`. One induction over `Ty`
carries both, which is the shape `Denote/Den.lean`'s own `FirstOrder` proof uses.

The spine half is parameterised over **two readers** related by "same, or this is the name that
moved". That covers both instances: `.inst` reads `ivarOf` at the two heaps (which differ at
`x`, and only for `self`), and `.clos` reads `closLocal`, which reads *frames* and does not
differ at all.

Every arm is then one of three kinds. The **shape** arms read
`classPayload?`/`ancestors`/`classNamed?`/the payload, all pinned by `Mut`. The **spine** arms
are where the write shows, and `ivarAgree` says the spine claims `τ` of the name that moved, so
`denM τ m₂ v` closes it. The **arrow** arms quantify over `Later`-futures, and the write is one
(`IvarWrite.later`), so `Later.trans` does the work — which is exactly why `ivarAgree` lets
them through unexamined. -/
theorem denM_ivarWrite {x : String} {v selfV : Value} {m m₂ : Machine} {τ : Ty}
    (hw : IvarWrite x v selfV m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (hv : denM τ m v) :
    ∀ (σ : Ty),
      (∀ w, Ratchet.ivarAgree x τ σ = true → denM σ m w → denM σ m₂ w) ∧
      (∀ (seen : List String) (g g' : String → Value),
        (∀ y, g' y = g y ∨ (y = x ∧ g' y = v)) →
        Ratchet.ivarAgree x τ σ = true → denSpineFrom seen σ m g → denSpineFrom seen σ m₂ g') := by
  intro σ
  induction σ with
  | int =>
    exact ⟨fun w _ h => by rw [denM] at h ⊢; exact h,
           fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | float =>
    exact ⟨fun w _ h => by rw [denM] at h ⊢; exact h,
           fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | sym =>
    exact ⟨fun w _ h => by rw [denM] at h ⊢; exact h,
           fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | bool =>
    exact ⟨fun w _ h => by rw [denM] at h ⊢; exact h,
           fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | nilT =>
    exact ⟨fun w _ h => by rw [denM] at h ⊢; exact h,
           fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | any =>
    exact ⟨fun w _ _ => by rw [denM]; trivial,
           fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | never =>
    exact ⟨fun w _ h => by rw [denM] at h; exact h.elim,
           fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | cls n =>
    exact ⟨fun w _ h => by rw [denM] at h ⊢; rw [hw.toMut.isANameEq hsat]; exact h,
           fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | clsOf n =>
    exact ⟨fun w _ h => by rw [denM] at h ⊢; rw [hw.toMut.isClassRefNamedEq]; exact h,
           fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | nilable ρ ih =>
    refine ⟨fun w hag h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [Ratchet.ivarAgree] at hag
    rw [denM] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (ih.1 w hag h)
  | union σ' ν ihσ ihν =>
    refine ⟨fun w hag h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [Ratchet.ivarAgree, Bool.and_eq_true] at hag
    rw [denM] at h ⊢
    rcases h with h | h
    · exact Or.inl (ihσ.1 w hag.1 h)
    · exact Or.inr (ihν.1 w hag.2 h)
  | arrayOf e ih =>
    refine ⟨fun w hag h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [Ratchet.ivarAgree] at hag
    rw [denM] at h ⊢
    obtain ⟨xs, hxs, hall⟩ := h
    exact ⟨xs, by rw [hw.toMut.arrElems]; exact hxs, fun y hy => ih.1 y hag (hall y hy)⟩
  | hashOf k' ν ihk ihν =>
    refine ⟨fun w hag h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [Ratchet.ivarAgree, Bool.and_eq_true] at hag
    rw [denM] at h ⊢
    obtain ⟨es, hes, hall⟩ := h
    refine ⟨es, by rw [hw.toMut.hshEntries]; exact hes, fun p hp => ?_⟩
    exact ⟨ihk.1 p.1 hag.1 (hall p hp).1, ihν.1 p.2 hag.2 (hall p hp).2⟩
  | sameAs y ρ ih =>
    refine ⟨fun w hag h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [Ratchet.ivarAgree] at hag
    rw [denM] at h ⊢
    exact ih.1 w hag h
  | inst n I ihI =>
    refine ⟨fun w hag h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    obtain ⟨hex, hsp⟩ := h
    rw [Ratchet.ivarAgree, Bool.and_eq_true] at hag
    refine ⟨by rw [hw.toMut.isExactInstEq]; exact hex, ?_⟩
    -- the object's own ivars: `x` moved (and only if the object *is* `self`), the rest did not
    refine ihI.2 [] (ivarOf m.heap w) (ivarOf m₂.heap w) (fun y => ?_) hag.2 hsp
    by_cases hy : y = x
    · by_cases hws : w = selfV
      · subst hws; exact Or.inr ⟨hy, by rw [hw.self y, if_pos hy]⟩
      · exact Or.inl (hw.other w hws y)
    · by_cases hws : w = selfV
      · subst hws; exact Or.inl (by rw [hw.self y, if_neg hy])
      · exact Or.inl (hw.other w hws y)
  | ivar0 =>
    exact ⟨fun w _ h => by rw [denM] at h; exact h.elim,
           fun seen g g' _ _ h => by rw [denSpineFrom] at h ⊢; trivial⟩
  | ivarCons y ρ rest ihρ ihrest =>
    refine ⟨fun w _ h => by rw [denM] at h; exact h.elim, fun seen g g' hg hag h => ?_⟩
    rw [Ratchet.ivarAgree, Bool.and_eq_true, Bool.and_eq_true] at hag
    obtain ⟨⟨hyx, hagρ⟩, hagrest⟩ := hag
    rw [denSpineFrom] at h ⊢
    obtain ⟨hhead, htail⟩ := h
    refine ⟨?_, ihrest.2 (y :: seen) g g' hg hagrest htail⟩
    rcases hhead with hs | hd
    · exact Or.inl hs
    · refine Or.inr ?_
      rcases hg y with hgy | ⟨hyx', hgy⟩
      · rw [hgy]; exact ihρ.1 (g y) hagρ hd
      · -- **the entry that moved**, and the one place the recursion is not on the value.
        -- `ivarAgree` says the spine claims `τ` of it, and what is owed is `denM τ m₂ v` —
        -- which is this theorem at `ρ = τ`, a *strict subterm* of the `σ` being inducted on.
        -- So the induction hypothesis `ihρ` discharges it from `hv`, and `hv` can be stated
        -- at the machine *before* the write. Taking it after would be circular: the rung has
        -- no way to know `denM τ m₂ v` except by this transport.
        rw [hgy]
        have hρτ : ρ = τ := by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hyx
          rcases hyx with h' | h'
          · exact absurd hyx' h'
          · exact ty_eq_of_beq h'
        exact ihρ.1 v (hρτ ▸ hagρ) (hρτ ▸ hv)
  | arrow0 r ihr =>
    -- **the `Later` arm**: `ivarAgree` waves arrows through, and this is why
    refine ⟨fun w _ h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    obtain ⟨hproc, harr⟩ := h
    refine ⟨by rw [hw.toMut.isProcVEq]; exact hproc, fun m₃ hlat => ?_⟩
    exact harr m₃ ((hw.later hsat).trans hlat)
  | arrowCons p rest ihp ihrest =>
    refine ⟨fun w _ h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    obtain ⟨hproc, harr⟩ := h
    refine ⟨by rw [hw.toMut.isProcVEq]; exact hproc, fun m₃ hlat => ?_⟩
    exact harr m₃ ((hw.later hsat).trans hlat)
  | clos idx cap selfT ihcap ihself =>
    -- **not** `Later`-quantified: it reads the captured frame and creation `self` at *this*
    -- machine, so both components are checked by `ivarAgree` and transported here.
    refine ⟨fun w hag h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [Ratchet.ivarAgree, Bool.and_eq_true] at hag
    rw [denM] at h ⊢
    obtain ⟨cl, hcl, hsp, hself⟩ := h
    refine ⟨cl, by rw [hw.toMut.procClosure]; exact hcl, ?_, ?_⟩
    · -- the reader is a `frames` reader, and `frames` did not move
      refine ihcap.2 [] (closLocal m cl) (closLocal m₂ cl) (fun y => ?_) hag.1 hsp
      exact Or.inl (by rw [hw.toMut.closLocalEq])
    · rcases hself with hn | hd
      · exact Or.inl hn
      · exact Or.inr (by rw [hw.toMut.closSelfEq]; exact ihself.1 _ hag.2 hd)

/-- **The right-hand side's own type, after its own write.** `ivarAgree x τ τ` is the guard
that makes this available, and the guard is not vacuous: it says `τ`'s spine, if it mentions
`@x` at all, mentions it at `τ` — which for a well-founded `Ty` means it does not mention it. -/
theorem denM_ivarWrite_post {x : String} {v selfV : Value} {m m₂ : Machine} {τ : Ty}
    (hw : IvarWrite x v selfV m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (hττ : Ratchet.ivarAgree x τ τ = true) (hv : denM τ m v) : denM τ m₂ v :=
  (denM_ivarWrite hw hsat hv τ).1 v hττ hv

/-! ## The `self` spine across the write

`SelfSpineOk` is the one `StateOk` component the write actually moves, and `ivarSet` is how
the rule says it moves. Three lemmas: a walk over the *unchanged* part (where `@x` is already
shadowed, so its entry is never read), the walk over `ivarSet`, and the completeness conjunct.
-/

/-- **`@x` is shadowed, so the write is invisible.** Every entry this walk reads is at a name
other than `x` — either because the entry's name differs, or because an earlier entry claimed
`x` and put it in `seen`. -/
theorem denSpineFrom_ivarWrite_skip {x : String} {v selfV : Value} {m m₂ : Machine} {τ : Ty}
    (hw : IvarWrite x v selfV m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (hv : denM τ m v) :
    ∀ (I : Ty) (seen : List String), x ∈ seen → Ratchet.ivarAgreeIvars x τ I = true →
      denSpineFrom seen I m (ivarOf m.heap selfV) →
      denSpineFrom seen I m₂ (ivarOf m₂.heap selfV)
  | .ivar0, seen, _, _, _ => by rw [denSpineFrom]; trivial
  | .ivarCons n σ rest, seen, hx, hag, h => by
    rw [Ratchet.ivarAgreeIvars, Bool.and_eq_true, Bool.or_eq_true] at hag
    rw [denSpineFrom] at h ⊢
    refine ⟨?_, denSpineFrom_ivarWrite_skip hw hsat hv rest (n :: seen)
      (List.mem_cons_of_mem _ hx) hag.2 h.2⟩
    by_cases hnx : n = x
    · exact Or.inl (hnx ▸ hx)
    · rcases h.1 with hs | hd
      · exact Or.inl hs
      · refine Or.inr ?_
        rw [hw.self n, if_neg hnx]
        refine (denM_ivarWrite hw hsat hv σ).1 _ ?_ hd
        rcases hag.1 with h' | h'
        · exact absurd (of_decide_eq_true (by simpa using h')) hnx
        · exact h'
  | .int, _, _, _, h | .float, _, _, _, h | .sym, _, _, _, h | .bool, _, _, _, h
  | .nilT, _, _, _, h | .any, _, _, _, h | .never, _, _, _, h | .cls _, _, _, _, h
  | .clsOf _, _, _, _, h | .nilable _, _, _, _, h | .union _ _, _, _, _, h
  | .arrayOf _, _, _, _, h | .hashOf _ _, _, _, _, h | .inst _ _, _, _, _, h
  | .sameAs _ _, _, _, _, h | .arrow0 _, _, _, _, h | .arrowCons .., _, _, _, h
  | .clos .., _, _, _, h => absurd h (by simp [denSpineFrom])

/-- **The walk over the spine the rule produces.** At `@x` the new value is read and `τ` is what
`Judge` claims of it; everywhere else the reader is unmoved and `ivarAgreeIvars` supplies the
agreement `denM_ivarWrite` needs. -/
theorem denSpineFrom_ivarWrite_set {x : String} {v selfV : Value} {m m₂ : Machine} {τ : Ty}
    (hw : IvarWrite x v selfV m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (hττ : Ratchet.ivarAgree x τ τ = true) (hv : denM τ m v) :
    ∀ (I : Ty) (seen : List String), Ratchet.ivarAgreeIvars x τ I = true →
      denSpineFrom seen I m (ivarOf m.heap selfV) →
      denSpineFrom seen (Ratchet.ivarSet I x τ) m₂ (ivarOf m₂.heap selfV)
  | .ivar0, seen, _, _ => by
    rw [Ratchet.ivarSet, denSpineFrom]
    exact ⟨Or.inr (by rw [hw.self x, if_pos rfl]; exact denM_ivarWrite_post hw hsat hττ hv),
      by rw [denSpineFrom]; trivial⟩
  | .ivarCons n σ rest, seen, hag, h => by
    rw [Ratchet.ivarAgreeIvars, Bool.and_eq_true, Bool.or_eq_true] at hag
    rw [denSpineFrom] at h
    rw [Ratchet.ivarSet]
    by_cases hnx : n = x
    · -- the entry that moved: the new type is `τ`, and `rest`'s own `@x` entry (if it has one)
      -- is now shadowed by `seen`
      subst hnx
      rw [if_pos (by simp), denSpineFrom]
      exact ⟨Or.inr (by rw [hw.self n, if_pos rfl]; exact denM_ivarWrite_post hw hsat hττ hv),
        denSpineFrom_ivarWrite_skip hw hsat hv rest (n :: seen) (List.mem_cons_self ..) hag.2 h.2⟩
    · rw [if_neg (by simpa using hnx), denSpineFrom]
      refine ⟨?_, denSpineFrom_ivarWrite_set hw hsat hττ hv rest (n :: seen) hag.2 h.2⟩
      rcases h.1 with hs | hd
      · exact Or.inl hs
      · refine Or.inr ?_
        rw [hw.self n, if_neg hnx]
        refine (denM_ivarWrite hw hsat hv σ).1 _ ?_ hd
        rcases hag.1 with h' | h'
        · exact absurd (of_decide_eq_true (by simpa using h')) hnx
        · exact h'
  | .int, _, _, h | .float, _, _, h | .sym, _, _, h | .bool, _, _, h
  | .nilT, _, _, h | .any, _, _, h | .never, _, _, h | .cls _, _, _, h
  | .clsOf _, _, _, h | .nilable _, _, _, h | .union _ _, _, _, h
  | .arrayOf _, _, _, h | .hashOf _ _, _, _, h | .inst _ _, _, _, h
  | .sameAs _ _, _, _, h | .arrow0 _, _, _, h | .arrowCons .., _, _, h
  | .clos .., _, _, h => absurd h (by simp [denSpineFrom])

/-- **A walk that succeeds proves the spine is well formed all the way down** — which is what
lets `ivarSet` be read as "and now `@x` is in it". Needed for `SelfSpineOk`'s completeness
conjunct, whose contrapositive is exactly "`@x` is not absent from the new spine". -/
theorem ivarGet?_ivarSet_hit_of_walk : ∀ (I : Ty) (seen : List String) (m : Machine)
    (g : String → Value) (x : String) (ρ : Ty),
    denSpineFrom seen I m g → Ratchet.ivarGet? (Ratchet.ivarSet I x ρ) x = some ρ
  | .ivar0, _, _, _, x, ρ, _ => by simp [Ratchet.ivarSet, Ratchet.ivarGet?]
  | .ivarCons n σ rest, seen, m, g, x, ρ, h => by
    rw [denSpineFrom] at h
    rw [Ratchet.ivarSet]
    by_cases hnx : n = x
    · subst hnx; rw [if_pos (by simp)]; simp [Ratchet.ivarGet?]
    · rw [if_neg (by simpa using hnx), Ratchet.ivarGet?, if_neg (by simpa using hnx)]
      exact ivarGet?_ivarSet_hit_of_walk rest (n :: seen) m g x ρ h.2
  | .int, _, _, _, _, _, h | .float, _, _, _, _, _, h | .sym, _, _, _, _, _, h
  | .bool, _, _, _, _, _, h | .nilT, _, _, _, _, _, h | .any, _, _, _, _, _, h
  | .never, _, _, _, _, _, h | .cls _, _, _, _, _, _, h | .clsOf _, _, _, _, _, _, h
  | .nilable _, _, _, _, _, _, h | .union _ _, _, _, _, _, _, h
  | .arrayOf _, _, _, _, _, _, h | .hashOf _ _, _, _, _, _, _, h
  | .inst _ _, _, _, _, _, _, h | .sameAs _ _, _, _, _, _, _, h
  | .arrow0 _, _, _, _, _, _, h | .arrowCons .., _, _, _, _, _, h
  | .clos .., _, _, _, _, _, h => absurd h (by simp [denSpineFrom])

/-- **`SelfSpineOk` across the write**, both conjuncts. -/
theorem selfSpineOk_ivarWrite {x : String} {v : Value} {m m₂ : Machine} {τ I : Ty}
    (hw : IvarWrite x v m.currentFrame.self m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (hττ : Ratchet.ivarAgree x τ τ = true) (hv : denM τ m v)
    (hag : Ratchet.ivarAgreeIvars x τ I = true) (h : SelfSpineOk I m) :
    SelfSpineOk (Ratchet.ivarSet I x τ) m₂ := by
  refine ⟨?_, ?_⟩
  · rw [hw.toMut.currentFrame]
    exact denSpineFrom_ivarWrite_set hw hsat hττ hv I [] hag h.1
  · intro y hy
    rw [hw.toMut.currentFrame]
    by_cases hyx : y = x
    · subst hyx
      rw [ivarGet?_ivarSet_hit_of_walk I [] m _ y τ h.1] at hy
      exact absurd hy (by simp)
    · rw [hw.self y, if_neg hyx]
      exact h.2 y (ivarGet?_ivarSet_none I x τ y hy)

#print axioms selfSpineOk_ivarWrite

/-! ## The nineteen shape-shaped components

Each of these is `Denote/Sem/State.lean`'s `.ext` twin with `Ext`'s interface swapped for
`Mut`'s. The proofs are the same proofs — every clause reads the heap only through
`classPayload?`, the ancestor walk, `classNamed?`, `constLookup` or `methodOn`, and `Mut` pins
all five — which is precisely the claim `ivarAsgnOk`'s docstring makes when it says the
components it does *not* guard "read only the heap's shape". Stating them separately rather
than factoring a common interface out of `Ext` and `Mut` keeps the change local: `Ext` grows
the heap and `Mut` does not, so the two relations agree on the shape reads and on nothing else.
-/

theorem CoreOk.mut {m m₂ : Machine} (hw : Mut m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (hc : CoreOk m.heap) : CoreOk m₂.heap where
  basicSelf := by rw [hw.ancestors hsat]; exact hc.basicSelf
  stringNamed := by rw [hw.classNamedEq]; exact hc.stringNamed
  stringSelf := by rw [hw.ancestors hsat]; exact hc.stringSelf
  stringBasic := by rw [hw.ancestors hsat]; exact hc.stringBasic
  regexpNamed := by rw [hw.classNamedEq]; exact hc.regexpNamed
  regexpSelf := by rw [hw.ancestors hsat]; exact hc.regexpSelf
  regexpBasic := by rw [hw.ancestors hsat]; exact hc.regexpBasic
  procBasic := by rw [hw.ancestors hsat]; exact hc.procBasic
  coreNamed := by
    intro n hn v hv
    exact hc.coreNamed n hn v (by rw [← hw.constLookupEq]; exact hv) |>.imp
      (fun o ho => ⟨ho.1, by rw [hw.classPayload]; exact ho.2⟩)

theorem ConstScopeOk.mut {m m₂ : Machine} (hw : Mut m m₂)
    (hsat : RubyCore.Proof.Saturated m.heap) (h : ConstScopeOk m) : ConstScopeOk m₂ := by
  intro n
  rw [show constResolveAt m₂ n = constResolveAt m n by
        simp only [constResolveAt, constOwn, constLookupFrom, hw.classPayload,
          hw.ancestors hsat, hw.currentFrame],
     show constLookup m₂.heap n = constLookup m.heap n from hw.constLookupEq n]
  exact h n

theorem NestedClassesOk.mut {C : CTable} {m m₂ : Machine} (hw : Mut m m₂)
    (hsat : RubyCore.Proof.Saturated m.heap) (h : NestedClassesOk C m) :
    NestedClassesOk C m₂ := by
  intro owner n c hc k v hcn hlk
  rw [hw.classNamedEq] at hcn
  simp only [constLookupFrom, hw.classPayload, hw.ancestors hsat] at hlk
  rw [hw.isClassRefNamedEq]
  exact h owner n c hc k v hcn hlk

theorem QueryOk.mut {κ : Ctx} {m m₂ : Machine} (hw : Mut m m₂)
    (hsat : RubyCore.Proof.Saturated m.heap) (h : QueryOk κ m) : QueryOk κ m₂ := by
  intro mname bid hmem hfree k
  obtain ⟨h1, h2⟩ := h mname bid hmem hfree k
  refine ⟨?_, ?_⟩
  · intro owner md hfound
    rw [hw.methodOn hsat] at hfound
    obtain ⟨hb, hu, hv, hp, hsh⟩ := h1 owner md hfound
    refine ⟨hb, hu, hv, hp, ?_⟩
    simp only [Interp.crubyShadow, className, hw.classPayload, hw.ancestors hsat] at hsh ⊢
    exact hsh
  · intro hnone o md hfound
    rw [hw.methodOn hsat] at hnone hfound
    exact h2 hnone o md hfound

theorem ClsQueryOk.mut {κ : Ctx} {m m₂ : Machine} (hw : Mut m m₂)
    (hsat : RubyCore.Proof.Saturated m.heap) (h : ClsQueryOk κ m) : ClsQueryOk κ m₂ := by
  intro mname bid hmem hfree o hp
  rw [hw.classPayload] at hp
  obtain ⟨h1, h2⟩ := h mname bid hmem hfree o hp
  have hm : ∀ n, Interp.methodOn m₂.heap (RubyCore.classOf m₂.heap (.ref o)) n
      = Interp.methodOn m.heap (RubyCore.classOf m.heap (.ref o)) n := by
    intro n; rw [hw.classOf]; exact hw.methodOn hsat _ n
  refine ⟨?_, ?_⟩
  · intro owner md hfound
    rw [hm] at hfound
    obtain ⟨hb, hu, hv, hpre, hsh⟩ := h1 owner md hfound
    refine ⟨hb, hu, hv, hpre, ?_⟩
    simp only [hw.classOf, Interp.crubyShadow, className, hw.classPayload,
      hw.ancestors hsat] at hsh ⊢
    exact hsh
  · intro hnone o₂ md hfound
    rw [hm] at hnone hfound
    exact h2 hnone o₂ md hfound

theorem NilQueryOk.mut {κ : Ctx} {m m₂ : Machine} (hw : Mut m m₂)
    (hsat : RubyCore.Proof.Saturated m.heap) (h : NilQueryOk κ m) : NilQueryOk κ m₂ := by
  intro hfree k
  obtain ⟨h1, h2⟩ := h hfree k
  refine ⟨?_, ?_⟩
  · intro owner md hfound
    rw [hw.methodOn hsat] at hfound
    obtain ⟨hb, hu, hv, hp, hsh⟩ := h1 owner md hfound
    refine ⟨hb, hu, hv, hp, ?_⟩
    simp only [Interp.crubyShadow, className, hw.classPayload, hw.ancestors hsat] at hsh ⊢
    exact hsh
  · intro hnone o₂ md hfound
    rw [hw.methodOn hsat] at hnone hfound
    exact h2 hnone o₂ md hfound

theorem BaseChainsOk.mut {κ : Ctx} {m m₂ : Machine} (hw : Mut m m₂)
    (hsat : RubyCore.Proof.Saturated m.heap) (h : BaseChainsOk κ m) : BaseChainsOk κ m₂ := by
  intro base ch hmem
  obtain ⟨hpos, hneg⟩ := h base ch hmem
  refine ⟨fun hcf => ?_, fun hok => ?_⟩
  · obtain ⟨h0, h1⟩ := hpos hcf
    refine ⟨fun bn hbn => by rw [hw.classNamedEq]; exact h0 bn hbn, fun cn hcn => ?_⟩
    obtain ⟨j, hj, hanc⟩ := h1 cn hcn
    exact ⟨j, by rw [hw.classNamedEq]; exact hj, by rw [hw.ancestors hsat]; exact hanc⟩
  · obtain ⟨h2, h3⟩ := hneg hok
    refine ⟨fun cn j hg hj hanc => ?_,
      fun k hk => h3 k (by rw [hw.ancestors hsat] at hk; exact hk)⟩
    rw [hw.classNamedEq] at hj
    rw [hw.ancestors hsat] at hanc
    exact h2 cn j hg hj hanc

theorem DeclClassOk.mut {κ : Ctx} {m m₂ : Machine} (hw : Mut m m₂)
    (hsat : RubyCore.Proof.Saturated m.heap) (h : DeclClassOk κ m) : DeclClassOk κ m₂ := by
  intro c hc k hcn
  rw [hw.classNamedEq] at hcn
  obtain ⟨hroot, hcls, hmod, hism, hnew, hinit, hchain⟩ := h c hc k hcn
  have hm : ∀ n, Interp.methodOn m₂.heap (RubyCore.classOf m₂.heap (.ref k)) n
      = Interp.methodOn m.heap (RubyCore.classOf m.heap (.ref k)) n := by
    intro n; rw [hw.classOf]; exact hw.methodOn hsat _ n
  refine ⟨by rw [hw.ancestors hsat]; exact hroot, hcls, hmod,
    by rw [hw.classPayload]; exact hism, ?_, ?_, ?_⟩
  · intro hsm
    obtain ⟨h1, h2⟩ := hnew hsm
    refine ⟨?_, ?_⟩
    · intro owner md hfound
      rw [hm] at hfound
      obtain ⟨hb, hu, hv, hp, hsh⟩ := h1 owner md hfound
      refine ⟨hb, hu, hv, hp, ?_⟩
      simp only [hw.classOf, Interp.crubyShadow, className, hw.classPayload,
        hw.ancestors hsat] at hsh ⊢
      exact hsh
    · intro hnone o₂ md hfound
      rw [hm] at hnone hfound
      exact h2 hnone o₂ md hfound
  · intro hct
    have hi := hinit hct
    simp only [Interp.userInit?, Interp.methodOn, hw.classPayload, hw.ancestors hsat] at hi ⊢
    exact hi
  · intro ch hch hmf
    obtain ⟨h1, h2⟩ := hchain ch hch hmf
    refine ⟨fun cn hcnm => ?_, fun cn j hj hanc => ?_⟩
    · obtain ⟨j, hj, hanc⟩ := h1 cn hcnm
      exact ⟨j, by rw [hw.classNamedEq]; exact hj, by rw [hw.ancestors hsat]; exact hanc⟩
    · rw [hw.classNamedEq] at hj
      rw [hw.ancestors hsat] at hanc
      exact h2 cn j hj hanc

/-! ## Reading `ivarAsgnOk`

Two projections, so the transport below can spend the guard one type at a time. -/

theorem ivarAgree_stripAlias {x : String} {τ σ : Ty} (h : Ratchet.ivarAgree x τ σ = true) :
    Ratchet.ivarAgree x τ (Ratchet.stripAlias σ) = true := by
  cases σ <;> simpa [Ratchet.stripAlias, Ratchet.ivarAgree] using h

theorem ivarAgree_of_envGet? {x : String} {τ : Ty} : ∀ (Γ : Env) (y : String) (σ : Ty),
    Ratchet.ivarAgreeEnv x τ Γ = true → Ratchet.envGet? Γ y = some σ →
    Ratchet.ivarAgree x τ σ = true
  | [], y, σ, _, hg => by simp [Ratchet.envGet?] at hg
  | (z, ρ) :: Γ, y, σ, hall, hg => by
    rw [Ratchet.ivarAgreeEnv, List.all_cons, Bool.and_eq_true] at hall
    by_cases hz : z = y
    · subst hz
      rw [envGet?_cons_self] at hg
      simp only [Option.some.injEq] at hg
      exact hg ▸ hall.1
    · rw [envGet?_cons_ne ρ Γ hz] at hg
      exact ivarAgree_of_envGet? Γ y σ hall.2 hg

/-- …and through `constGet?`, which is a `findSome?` over the paths a name can resolve along. -/
theorem ivarAgree_of_constGet? {x : String} {τ : Ty} {Γ : Env}
    (hall : Ratchet.ivarAgreeEnv x τ Γ = true) :
    ∀ (ks : List String) (σ : Ty),
      ks.findSome? (fun k => Ratchet.envGet? Γ k) = some σ → Ratchet.ivarAgree x τ σ = true
  | [], σ, hg => by simp [List.findSome?] at hg
  | k :: ks, σ, hg => by
    rw [List.findSome?_cons] at hg
    cases hk : Ratchet.envGet? Γ k with
    | none =>
      rw [hk] at hg
      simp only at hg
      exact ivarAgree_of_constGet? hall ks σ hg
    | some ρ =>
      rw [hk] at hg
      simp only [Option.some.injEq] at hg
      exact hg ▸ ivarAgree_of_envGet? Γ k ρ hall hk

/-! ## `StateOk` across an instance-variable write

The rung's whole state obligation, in one place. The five guarded components are the five
`ivarAsgnOk` names, plus `SelfSpineOk` — which is not guarded because it is not *preserved*:
`ivarSet` says how it moves. -/

theorem StateOk_ivarWrite {κ : Ctx} {Γ : Env} {I τ : Ty} {x : String} {v : Value}
    {m m₂ : Machine} (h : StateOk κ Γ I m)
    (hw : IvarWrite x v m.currentFrame.self m m₂) (hv : denM τ m v)
    (hok : Ratchet.ivarAsgnOk κ x τ Γ I = true) :
    StateOk κ Γ (Ratchet.ivarSet I x τ) m₂ := by
  have hsat : RubyCore.Proof.Saturated m.heap := h.sat
  have hmut : Mut m m₂ := hw.toMut
  have hden : ∀ (σ : Ty) (w : Value), Ratchet.ivarAgree x τ σ = true → denM σ m w →
      denM σ m₂ w := fun σ w => (denM_ivarWrite hw hsat hv σ).1 w
  rw [Ratchet.ivarAsgnOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨hΓ, hττ⟩, hself⟩, hblk⟩, hconsts⟩, hI⟩ := hok
  exact {
    sat := RubyCore.Proof.Saturated_grow hmut.shapeAgree (Nat.le_of_eq hmut.size.symm) h.sat
    core := CoreOk.mut hmut hsat h.core
    frameInRange := by
      have hf := h.frameInRange
      unfold FrameInRange at hf ⊢
      rw [hmut.stack, hmut.frames]; exact hf
    env := by
      refine ⟨?_, ?_⟩
      · intro y σ hy
        obtain ⟨hd, hid⟩ := h.env.1 y σ hy
        refine ⟨?_, ?_⟩
        · rw [hmut.getLocal]
          exact hden _ _ (ivarAgree_stripAlias (ivarAgree_of_envGet? Γ y σ hΓ hy)) hd
        · intro z ρ hτ; rw [hmut.getLocal, hmut.getLocal]; exact hid z ρ hτ
      · intro y hy; rw [hmut.getLocal]; exact h.env.2 y hy
    selfSpine := selfSpineOk_ivarWrite hw hsat hττ hv hI h.selfSpine
    classes := by
      intro c hc
      obtain ⟨k, hk, hm⟩ := h.classes c hc
      refine ⟨k, by rw [hmut.classNamedEq]; exact hk, ?_⟩
      intro d hd
      obtain ⟨md, h1, h2⟩ := hm d hd
      exact ⟨md, by rw [hmut.classPayload]; exact h1, h2⟩
    defs := by
      intro d hd
      obtain ⟨md, h1, h2⟩ := h.defs d hd
      exact ⟨md, by rw [hmut.classPayload]; exact h1, h2⟩
    asms := by
      intro a ha m₃ he₃ args hargs w m' hs
      exact h.asms a ha m₃ ((hw.later hsat).trans he₃) args hargs w m' hs
    frame := by
      have h2 := h.frame
      unfold FrameOk at h2 ⊢
      cases hf : κ.frame with
      | none => rw [hf] at h2; rw [hmut.currentFrame]; exact h2
      | some f =>
        rw [hf] at h2
        exact ⟨by rw [hmut.currentFrame]; exact h2.1,
               by rw [hmut.currentFrame, hmut.isANameEq hsat]; exact h2.2⟩
    closures := trivial
    blockTy := by
      have h2 := h.blockTy
      unfold BlockTyOk at h2 ⊢
      cases hb : κ.blockTy with
      | none => rw [hb] at h2; rw [hmut.currentFrame]; exact h2
      | some β =>
        rw [hb] at h2
        obtain ⟨b, hb1, hb2⟩ := h2
        refine ⟨b, by rw [hmut.currentFrame]; exact hb1, hden _ _ ?_ hb2⟩
        rw [hb] at hblk; exact hblk
    selfTy := by
      have h2 := h.selfTy
      unfold SelfTyOk at h2 ⊢
      cases hσ : κ.selfTy with
      | none => trivial
      | some σ =>
        rw [hσ] at h2
        rw [hmut.currentFrame]
        refine hden _ _ ?_ h2
        rw [hσ] at hself; exact hself
    constPaths := by
      intro owner n σ k hk hcn w hvv
      rw [hmut.classNamedEq] at hcn
      simp only [constLookupFrom, hmut.classPayload, hmut.ancestors hsat] at hvv
      exact hden _ _ (ivarAgree_of_envGet? κ.consts _ σ hconsts hk)
        (h.constPaths owner n σ k hk hcn w hvv)
    nested := NestedClassesOk.mut hmut hsat h.nested
    consts := by
      intro n σ hn
      obtain ⟨w, hv1, hv2⟩ := h.consts n σ hn
      refine ⟨w, ?_, hden _ _ (ivarAgree_of_constGet? hconsts _ σ hn) hv2⟩
      rw [show constResolveAt m₂ n = constResolveAt m n by
        simp only [constResolveAt, constOwn, constLookupFrom, hmut.classPayload,
          hmut.ancestors hsat, hmut.currentFrame]]
      exact hv1
    privConsts := trivial
    constScope := ConstScopeOk.mut hmut hsat h.constScope
    exact := by
      intro k cp hk
      exact h.exact k cp (by rw [hmut.classPayload] at hk; exact hk)
    nameFree := by
      intro n hn o md hm
      refine h.nameFree n hn o md ?_
      rw [← hm, hmut.currentFrame, hmut.classOf]
      exact (hmut.methodOn hsat _ n).symm
    bareFree := by
      intro n hn hdef hself2
      rw [show lookup m₂.heap m₂.currentFrame.self n
            = lookup m.heap m.currentFrame.self n by
        rw [lookup_eq_methodOn, lookup_eq_methodOn, hmut.currentFrame, hmut.classOf]
        exact hmut.methodOn hsat _ n]
      exact h.bareFree n hn hdef hself2
    query := QueryOk.mut hmut hsat h.query
    clsQuery := ClsQueryOk.mut hmut hsat h.clsQuery
    declCls := DeclClassOk.mut hmut hsat h.declCls
    baseChains := BaseChainsOk.mut hmut hsat h.baseChains
    nilQuery := NilQueryOk.mut hmut hsat h.nilQuery
    missFree := by
      intro hfree hself2 o md hm
      refine h.missFree hfree hself2 o md ?_
      rw [← hm, hmut.currentFrame, hmut.classOf]
      exact (hmut.methodOn hsat _ "method_missing").symm
    selfLive := by
      intro o ho
      rw [hmut.currentFrame] at ho
      rw [hmut.size]
      exact h.selfLive o ho }

#print axioms StateOk_ivarWrite

end Ratchet.Denote
