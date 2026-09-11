import Denote.Sanity
import Denote.Sem.SafeKont
import Denote.Rules.VasgnStuck

/-!
# `Denote/Sem/NoProgress.lean` — `SemJudge` has no progress content, and the refutation that
says so

**The question**: `SemJudge`'s obligation is an implication with `Evals` on the **left**, so an
expression whose runs never reach `.value` satisfies it vacuously — at *every* type at once.
Does that make "well-typed implies stuck-free" a false theorem?

**The answer, in three parts.**

1. **Nothing in the tree claims it.** `Denote/Adequacy.lean` states `StuckFreeTarget`
   separately and records "Not implied by `AdequacyTarget`"; `Denote/Sem/Judge.lean`'s choice
   1 and `Denote/Sem/State.lean`'s `Evals` docstring both say partial correctness is
   deliberate. `../../../docs/semantics/answer-typed-judgments.md` §2.1 states it as the
   diagnosis: "`SemJudge` has real *preservation* content … and **no progress content at
   all**." So this is a documented gap, not an asserted falsehood.
2. **But it was only ever documented, never proved false** — and this package's own working
   rule is that a `Prop`-shaped named claim is one that can be attacked (`not_KontFrame`,
   `not_BuiltinsSeal`). `SemJudgeImpliesStuckFree` below is the claim, and
   `not_semJudgeImpliesStuckFree` is its refutation. It is now on file, so it cannot be
   reintroduced by accident.
3. **The witness is `break(1.foo)`**, and it is sharper than the obvious candidates:

   | candidate | `Evals` unsatisfiable? | `typeStuck`? | refutes? |
   |---|---|---|---|
   | a gated expression (`regexpLit`) | yes, structurally | **no** — `.unsupported` is not type-stuck | no |
   | `break` with no operand | yes (`jump_empty_never_value`) | **no** — `.stuck`, not `.uncaught` | no |
   | `1.foo` alone | **no** — a conformant machine may define it (see below) | yes | no |
   | **`break(1.foo)`** | **yes, for any operand** | **yes** | **yes** |

   The point of the fourth row: `.brk (some f)` can never return a value *whatever `f` does* —
   if `f` returns, the `jumpValK` turns the value into a `brkJ`; if `f` escapes, the escape
   passes through; either way a jump meets the empty continuation. So `Evals` is unsatisfiable
   **with no hypothesis about the heap at all**, which is what makes `SemJudge` hold
   unconditionally, while the operand's `NoMethodError` makes the run type-stuck.

## Why `1.foo` alone is *not* a witness, and why that is a second finding

The obvious attempt is an expression that just gets stuck. It does not work, and the reason is
`Denote/Sem/Frame.lean` §2: `StateOk` is a lower bound plus *partial* exactness.
`MethodsExact` permits any method marked `fromPrelude`, and `NameFreeOk` sharpens that to
"absent" only on the fixed list of names the rules reason from — `"foo"` is not on it. So
"`StateOk ctx0 [] .ivar0 m`" does **not** entail that `m` lacks an `Integer#foo`, and
`∀ m, StateOk … m → ¬ Evals m (1.foo) v m'` is not provable. Routing the vacuity through a
`break` sidesteps the heap entirely.

## What the answer type does about it

Exactly what §6 said: the escape becomes an `Answer` instead of an absent hypothesis.
`runA_brk` below is the contrast — the same run that `Evals` cannot see reports
`.ans (.esc (.brkJ w)) …`, and `Denote/Rules/WhileAnswer.lean`'s `AnswerOkAt` is the premise
shape that consumes it. The refutation is therefore not an argument against the ladder; it is
the measurement of what the second axis has to add, and `Denote/Sem/Invariant.lean` is the
shape that adds it.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The claim -/

/-- **The statement under suspicion**: semantic well-typedness implies stuck-freedom.
Refuted below. -/
def SemJudgeImpliesStuckFree : Prop :=
  ∀ (κ : Ctx) (Γ : Env) (I : Ty) (e : Ratchet.Expr) (τ : Ty) (κ' : Ctx) (Γ' : Env) (I' : Ty),
    SemJudge κ Γ I e τ κ' Γ' I' → StuckFreeAt κ Γ I e

/-! ## Vacuity, in general -/

/-- **The vacuity lemma.** An expression whose runs never return a value satisfies `SemJudge`
at *every* type, in every context, with every outgoing state. Two lines, and it is the whole
of the user-visible problem: the obligation's only hypothesis is the one thing such an
expression never supplies. -/
theorem semJudge_of_never_value {κ : Ctx} {Γ : Env} {I : Ty} {e : Ratchet.Expr} {κ' : Ctx}
    {Γ' : Env} {I' : Ty} (hp : Plain e) (h : ∀ m v m', ¬ Evals m e v m') :
    ∀ τ, SemJudge κ Γ I e τ κ' Γ' I' :=
  fun _ => ⟨hp, fun m _ v m' hev => absurd hev (h m v m')⟩

/-! ## The witness: a `break` never returns, whatever its operand does -/

theorem catchFree_jumpValK (k : RubyCore.JumpKind) :
    RubyCore.Proof.CatchFree [.jumpValK k] := by
  intro kk hk t; rcases List.mem_singleton.mp hk with rfl; simp

/-- Delivering a **value** to `break`'s operand frame turns it into a `brkJ` at the empty
continuation. `rfl`. -/
theorem stepFn_jumpValK_val (m : Machine) (w : Value) :
    Interp.stepFn (deliverA (.val w) m [.jumpValK .brkK])
      = .next { m with ctl := .jump (.brkJ w), kont := [] } := rfl

/-- Delivering an **escape** to it passes the escape through, also at the empty continuation. -/
theorem stepFn_jumpValK_esc (m : Machine) (j : Jump) :
    Interp.stepFn (deliverA (.esc j) m [.jumpValK .brkK])
      = .next { m with ctl := .jump j, kont := [] } := by
  cases j <;> rfl

/-- Entering `break e`: push the operand frame. `rfl`. -/
theorem stepFn_brk_push (m : Machine) (f : Ratchet.Expr) :
    Interp.stepFn (evalFrom m (.brk (some f)))
      = .next (pushK [.jumpValK .brkK] (evalFrom m f)) := rfl

/-- **`break e` never returns a value — for any `e`, from any machine, at any fuel.**

No hypothesis about the heap, the operand, or the context. Every route out of the operand ends
at a jump under the empty continuation, and `jump_empty_never_value` closes all of them. This
is the step the heap-dependent candidates could not take. -/
theorem evals_brk_never (f : Ratchet.Expr) :
    ∀ (m : Machine) (v : Value) (m' : Machine), ¬ Evals m (.brk (some f)) v m' := by
  intro m v m' ⟨fuel, hrun⟩
  match fuel with
  | 0 => exact absurd hrun (by simp [run_zero])
  | n + 1 =>
    simp only [run_succ, stepFn_brk_push] at hrun
    rw [run_pushK [.jumpValK .brkK] (catchFree_jumpValK .brkK) n (evalFrom m f)] at hrun
    cases hr : runA n (evalFrom m f) with
    | halt h => rw [hr] at hrun; cases h <;> exact absurd hrun (by simp [ARes.out, Halt.out])
    | oof m₀ => rw [hr] at hrun; exact absurd hrun (by simp [ARes.out])
    | ans a m₀ rest =>
      rw [hr] at hrun
      simp only [ARes.out] at hrun
      match rest with
      | 0 => exact absurd hrun (by simp [run_zero])
      | r + 1 =>
        rw [run_succ] at hrun
        cases a with
        | val w =>
          rw [stepFn_jumpValK_val] at hrun
          exact jump_empty_never_value r _ v m' ⟨_, rfl⟩ rfl hrun
        | esc j =>
          rw [stepFn_jumpValK_esc] at hrun
          exact jump_empty_never_value r _ v m' ⟨j, rfl⟩ rfl hrun

/-- …so it is `SemJudge`-well-typed at every type at once. -/
theorem semJudge_brk (κ : Ctx) (Γ : Env) (I : Ty) (f : Ratchet.Expr) (κ' : Ctx) (Γ' : Env)
    (I' : Ty) : ∀ τ, SemJudge κ Γ I (.brk (some f)) τ κ' Γ' I' :=
  semJudge_of_never_value trivial (evals_brk_never f)

/-- **`SemJudge` cannot tell `Integer` from `String`.** The two statements are incompatible as
*types* and both hold as *semantic judgments*. -/
example (κ : Ctx) (Γ : Env) (I : Ty) (f : Ratchet.Expr) :
    SemJudge κ Γ I (.brk (some f)) .int κ Γ I ∧
    SemJudge κ Γ I (.brk (some f)) (.cls "String") κ Γ I ∧
    SemJudge κ Γ I (.brk (some f)) .never κ Γ I :=
  ⟨semJudge_brk κ Γ I f κ Γ I .int, semJudge_brk κ Γ I f κ Γ I (.cls "String"),
   semJudge_brk κ Γ I f κ Γ I .never⟩

/-! ## The refutation

One `Bool`, checked by the `#guard` below — `Denote/Sanity.lean`'s discipline, for its
reason: `Interp.invoke` is compiled by well-founded recursion, so the run is not
`rfl`-reducible, and `native_decide` would cost `Lean.ofReduceBool`. -/

/-- `break(1.foo)` — the operand is a method no conformant machine's `Integer` has to have,
and the `break` is what makes the whole expression unable to return. -/
def brkBad : Ratchet.Expr := .brk (some (.send (some (.int 1)) "foo" [] none))

/-- The computation the refutation rests on: from the prelude-booted machine, `break(1.foo)`
reaches a type-stuck outcome. -/
def brkBadStuckB : Bool :=
  Semantics.typeStuck (Interp.run 200 (evalFrom bootMachine brkBad))

/-- **`SemJudgeImpliesStuckFree` is false.**

Both hypotheses are `#guard`ed below: `bootOkB` is `Denote/Sanity.lean`'s conformance witness
(`stateOk_boot`), and `brkBadStuckB` is the run. Everything else is unconditional. -/
theorem not_semJudgeImpliesStuckFree (hb : bootOkB = true) (hs : brkBadStuckB = true) :
    ¬ SemJudgeImpliesStuckFree := by
  intro h
  have hsf : StuckFreeAt Ratchet.ctx0 [] .ivar0 brkBad :=
    h Ratchet.ctx0 [] .ivar0 brkBad .int Ratchet.ctx0 [] .ivar0
      (semJudge_brk Ratchet.ctx0 [] .ivar0 _ Ratchet.ctx0 [] .ivar0 .int)
  have := hsf bootMachine (stateOk_boot hb) 200
  rw [← brkBadStuckB, hs] at this
  exact absurd this (by simp)

-- **The gate.**
#guard brkBadStuckB

/-! ## The contrast: the answer type does see it

Same run, read the other way. `Evals` is unsatisfiable here and `runA` is not: it reports the
escape, together with the machine it escaped from. That difference is the whole of
`../../../docs/semantics/answer-typed-judgments.md` §6, and it is why the second axis is
statable at all. -/

theorem runA_brk_val (m : Machine) (w : Value) (n : Nat) :
    runA (n + 1) { m with ctl := .jump (.brkJ w), kont := [] }
      = .ans (.esc (.brkJ w)) { m with ctl := .jump (.brkJ w), kont := [] } (n + 1) :=
  runA_ans rfl _

#print axioms semJudge_of_never_value
#print axioms evals_brk_never
#print axioms not_semJudgeImpliesStuckFree

end Ratchet.Denote
