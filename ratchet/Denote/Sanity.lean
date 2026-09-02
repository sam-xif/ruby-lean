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

/-- `CoreOk` as a `Bool`, so the four clauses are one computation. -/
def coreOkB (h : Heap) : Bool :=
  (ancestors h Boot.basicObjectId == [Boot.basicObjectId]) &&
  (classNamed? h "String" == some Boot.stringId) &&
  (ancestors h Boot.stringId).contains Boot.stringId &&
  (ancestors h Boot.stringId).contains Boot.basicObjectId

theorem coreOkB_sound {h : Heap} (hb : coreOkB h = true) : CoreOk h := by
  simp only [coreOkB, Bool.and_eq_true, beq_iff_eq] at hb
  exact ⟨hb.1.1.1, hb.1.1.2, hb.1.2, hb.2⟩

/-- The two frame facts `ctx0` asks of the starting machine: it is not inside a method body
and it was not called with a block. -/
def frameOkB (m : Machine) : Bool :=
  (m.currentFrame.kind != .method) && m.currentFrame.blk.isNone

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
  saturatedB bootMachine.heap && coreOkB bootMachine.heap && frameOkB bootMachine

/-- **The satisfiability witness.** `StateOk` holds at the real booted machine in the empty
context, so no obligation on the ladder is vacuously true for want of a conformant machine.

The hypothesis is discharged by the `#guard` below, at build time, against the same
prelude-booted heap the difftest SUT and `Denote/Examples.lean` use. -/
theorem stateOk_boot (hb : bootOkB = true) : StateOk Ratchet.ctx0 [] .ivar0 bootMachine := by
  simp only [bootOkB, frameOkB, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none]
    at hb
  exact
    { sat := Proof.saturatedB_sound hb.1.1
      core := coreOkB_sound hb.1.2
      env := by intro x τ hx; exact absurd hx (by simp [envGet?, Ratchet.ctx0])
      selfSpine := by simp [SelfSpineOk, denSpine]
      classes := by intro c hc; exact absurd hc (by simp [Ratchet.ctx0])
      defs := by intro d hd; exact absurd hd (by simp [Ratchet.ctx0])
      asms := by intro a ha; exact absurd ha (by simp [Ratchet.ctx0])
      frame := by simp only [FrameOk, Ratchet.ctx0]; exact hb.2.1
      closures := trivial
      blockTy := by simp only [BlockTyOk, Ratchet.ctx0]; exact hb.2.2
      selfTy := by simp [SelfTyOk, Ratchet.ctx0]
      consts := by intro p τ hp; exact absurd hp (by simp [envGet?, Ratchet.ctx0])
      privConsts := trivial }

-- **The gate.** If this fails, the ladder's hypothesis has no exhibited model and every
-- rung on it is suspect.
#guard bootOkB

#print axioms stateOk_boot

end Ratchet.Denote
