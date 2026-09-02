import Denote.Sem.State
import Ratchet.Validate
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

/-- The prelude-booted machine — the same one `Ratchet.Semantics.run` executes a rung from,
and the same one `Denote/Examples.lean`'s 31 guards observe. A boot failure falls back to a
machine that fails the checks below loudly rather than passing them vacuously. -/
def bootMachine : Machine :=
  match Semantics.bootedMachine with
  | .ok m => m
  | .error _ => Machine.init .nil

/-- `CoreOk` as a `Bool`, so its clauses are one computation. Seven of them since clink 48:
`Judge.regexpLit` added the `Regexp` row, exactly as `CoreOk`'s docstring said the `String`
one would be joined. -/
def coreOkB (h : Heap) : Bool :=
  (ancestors h Boot.basicObjectId == [Boot.basicObjectId]) &&
  (classNamed? h "String" == some Boot.stringId) &&
  (ancestors h Boot.stringId).contains Boot.stringId &&
  (ancestors h Boot.stringId).contains Boot.basicObjectId &&
  (classNamed? h "Regexp" == some Boot.regexpId) &&
  (ancestors h Boot.regexpId).contains Boot.regexpId &&
  (ancestors h Boot.regexpId).contains Boot.basicObjectId &&
  coreClsNames.all (fun n =>
    match constLookup h n with
    | some (.ref o) => (h.classPayload? o).isSome
    | some _ => false
    | none => true)

theorem coreOkB_sound {h : Heap} (hb : coreOkB h = true) : CoreOk h := by
  simp only [coreOkB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hb
  refine ⟨hb.1.1.1.1.1.1.1, hb.1.1.1.1.1.1.2, hb.1.1.1.1.1.2, hb.1.1.1.1.2, hb.1.1.1.2,
          hb.1.1.2, hb.1.2, ?_⟩
  intro n hn v hv
  have := hb.2 n hn
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
  (m.stack.headD 0 < m.frames.size) && selfIvarsEmptyB m

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
  topScopeB bootMachine

/-- **The satisfiability witness.** `StateOk` holds at the real booted machine in the empty
context, so no obligation on the ladder is vacuously true for want of a conformant machine.

The hypothesis is discharged by the `#guard` below, at build time, against the same
prelude-booted heap the difftest SUT and `Denote/Examples.lean` use. -/
theorem stateOk_boot (hb : bootOkB = true) : StateOk Ratchet.ctx0 [] .ivar0 bootMachine := by
  simp only [bootOkB, frameOkB, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none,
    decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hsat, hcore⟩, ⟨⟨hkind, hblk⟩, hfr⟩, hself⟩, htop⟩ := hb
  exact
    { sat := Proof.saturatedB_sound hsat
      core := coreOkB_sound hcore
      env := by intro x τ hx; exact absurd hx (by simp [envGet?, Ratchet.ctx0])
      selfSpine := ⟨by simp [denSpine], fun x _ => selfIvarsEmpty_sound hself x⟩
      classes := by intro c hc; exact absurd hc (by simp [Ratchet.ctx0])
      defs := by intro d hd; exact absurd hd (by simp [Ratchet.ctx0])
      asms := by intro a ha; exact absurd ha (by simp [Ratchet.ctx0])
      frameInRange := hfr
      frame := by simp only [FrameOk, Ratchet.ctx0]; exact hkind
      closures := trivial
      blockTy := by simp only [BlockTyOk, Ratchet.ctx0]; exact hblk
      selfTy := by simp [SelfTyOk, Ratchet.ctx0]
      consts := by
        intro p τ hp
        exact absurd hp (by simp [constGet?, Ratchet.constPaths, envGet?, Ratchet.ctx0])
      privConsts := trivial
      constScope := constScope_of_topScope htop }

-- **The gate.** If this fails, the ladder's hypothesis has no exhibited model and every
-- rung on it is suspect.
#guard bootOkB

#print axioms stateOk_boot

end Ratchet.Denote
