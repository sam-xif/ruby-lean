import Denote.Sem.SafeKont

/-!
# `Denote/Sem/AnswerValue.lean` — the *value* axis, out of the same equation

`Denote/Rules/WhileAnswer.lean` shows the answer type paying on the stuck-freedom axis, which
is the axis it was diagnosed from. The question this file answers is the other one: **does
the ladder's existing 48 rungs' foundation survive the restatement, or is this a second
machine?**

It survives, as a corollary. `run_split` — `Denote/Sem/Decompose.lean`'s 60-line induction,
the lemma every compound rung on the value axis consumes — is derived below from `run_pushK`
in twenty lines, with its hypotheses unchanged. So the answer type is not an alternative to
the value ladder; it is the ladder's decomposition with the discarded arms kept.

## Where `JumpOpaque` went

It is still a hypothesis of `run_split_A`, and that is the point rather than a
disappointment: a caller who wants to conclude that the *value* came out of the sub-run has
to rule the escape out somehow. What changed is **where** it is spent — one line, in the
`esc` arm, instead of being threaded through an induction. §6's "the escape case is a clause
rather than a missing hypothesis" is literally visible in the proof below: `hJ` is applied
once, in the branch named `esc`.

And a caller who does *not* want to rule it out no longer has to. `run_split` cannot be
applied at a continuation for which `JumpOpaque` is false (a loop, a `rescue`); the
answer-typed `run_pushK` can, and the escape arrives as an obligation instead of a
contradiction.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **`run_split`, derived.** Identical statement to `Denote/Sem/Decompose.lean`'s, same two
hypotheses, and no induction: the induction is `run_pushK`'s, and it is shared with the
stuck-freedom axis. -/
theorem run_split_A (K : List Kont) (hK : RubyCore.Proof.CatchFree K) (hJ : JumpOpaque K) :
    ∀ (fuel : Nat) (m : Machine) (v : Value) (m' : Machine),
      Interp.run fuel (pushK K m) = .value v m' →
      ∃ (n : Nat) (v₀ : Value) (m₀ : Machine),
        Interp.run n m = .value v₀ m₀ ∧ m₀.ctl = .value v₀ ∧ m₀.kont = [] ∧
        ∃ f2, Interp.run f2 (deliver m₀ v₀ K) = .value v m' := by
  intro fuel m v m' h
  rw [run_pushK K hK fuel m] at h
  cases hr : runA fuel m with
  | halt hh => rw [hr] at h; cases hh <;> exact absurd h (by simp [ARes.out, Halt.out])
  | oof m₀ => rw [hr] at h; exact absurd h (by simp [ARes.out])
  | ans a m₀ rest =>
    rw [hr] at h
    simp only [ARes.out] at h
    have hap : answerPoint m₀ = some a := answerPoint_of_ans fuel m a m₀ rest hr
    cases a with
    | esc j =>
      -- **the one line `JumpOpaque` is for**
      exact absurd h (hJ m₀ j rest v m')
    | val v₀ =>
      -- the answer point spells out the two projections the statement asks for
      have hc : m₀.ctl = .value v₀ := by
        cases hk : m₀.kont with
        | cons k r => rw [answerPoint, hk] at hap; simp at hap
        | nil =>
          cases hcc : m₀.ctl with
          | eval e => rw [answerPoint, hk] at hap; simp only at hap; rw [hcc] at hap; simp at hap
          | jump j => rw [answerPoint, hk] at hap; simp only at hap; rw [hcc] at hap; simp at hap
          | value w =>
            rw [answerPoint, hk] at hap; simp only at hap; rw [hcc] at hap
            simp only [Option.some.injEq] at hap
            injection hap with hw
            rw [hw]
      have hk : m₀.kont = [] := by
        cases hkk : m₀.kont with
        | nil => rfl
        | cons k r => rw [answerPoint, hkk] at hap; simp at hap
      -- the inner run reaches the same answer, and one more step turns it into `.value`
      refine ⟨fuel + 1, v₀, m₀, ?_, hc, hk, rest, h⟩
      have hadd := runA_add fuel m (.val v₀) m₀ rest hr 1
      rw [run_eq_out_nil (fuel + 1) m, hadd]
      simp only [ARes.out, deliverA_nil_self hap, run_succ]
      rw [show Interp.stepFn m₀ = .done v₀ m₀ by
        simp only [Interp.stepFn, hc, Interp.applyKont, hk]]

#print axioms run_split_A

/-! And `JumpOpaque` itself is now *derivable* where it used to be assumed, for any `K` whose
escape arms are known — it is `SafeKont K (fun a _ => a = .esc j) (· is not a value)` in
disguise. Recorded, not built: the ladder's existing `jumpOpaque_asgnK` is four lines and
nothing is waiting on a general form. -/


end Ratchet.Denote
