import Denote.Rules.Seq
import Denote.Sem.Decompose

/-!
# `Denote/Rules/SeqCons.lean` — the multi-statement sequence, decomposed

`Denote/Rules/Seq.lean` closes `JudgeSeq.last`, the singleton, and says why `JudgeSeq.cons` is
harder: the first statement of `e :: e' :: es` runs **under `.seqK rest`**, a non-empty
continuation, while `Evals` is defined at an empty one. That was the fifth stall point, and it
is cleared — `Denote/Sem/Decompose.lean`'s `run_split` is the frame rule, proved over the whole
of `stepFn`.

This file spends it. `evals_seq_cons` is the whole run-level content of `JudgeSeq.cons`:

> a run of `.seq (e :: e' :: es)` **is** a run of `e` followed by a run of `.seq (e' :: es)`

with both machines exhibited. Three obligations to `run_split`, and each is one computation:

* **`CatchFree [.seqK rest]`** — `.seqK` is not `.catchK`, and that is the whole of it.
* **`JumpOpaque [.seqK rest]`** — `unwind` has no `.seqK` arm, so a jump takes the default
  (pass through, continuation popped), which lands on `jump_empty_never_value`. Word for word
  `Denote/Sem/Decompose.lean`'s `jumpOpaque_asgnK`, which its docstring predicted would be
  "the shape every other rule's literal kont will follow".
* **The two one-step equalities** at either end: `evalExpr`'s `.seq` arm pushes exactly
  `pushK [.seqK rest]`, and `applyKont`'s `.seqK` arm lands on exactly what `evalFrom` of the
  tail sequence steps to.

**What this does *not* close, and it is worth being exact about it.** `Obl.JudgeSeq.cons`'s
second premise is at context **`κ.afterStmt e σ`** while its conclusion is at `κ`, so the rung
needs `StateOk` transported *both ways* across `afterStmt`:

* **up** (to apply premise 2): `StateOk κ Γ₁ I₁ m₁ → StateOk (κ.afterStmt e σ) Γ₁ I₁ m₁`, and
* **down** (to state the conclusion): `StateOk (κ.afterStmt e σ) Γ₂ I₂ m' → StateOk κ Γ₂ I₂ m'`.

`afterStmt` is the identity on every expression head except the five declarations
(`.def'`, `.class'`, `.module'`, `.casgn`, `.cpathAsgn` — read off `extendDefs`/
`extendClasses`/`extendConsts`/`extendPrivConsts`), so both directions are `rfl` when the first
statement is not a declaration. In general **neither holds, and they fail on *different*
components** — which is the fact worth recording, because it rules out the obvious repair.
`StateOk`'s table-reading components are monotone in opposite directions:

| direction of growth | components | which transport it gives |
|---|---|---|
| a bigger table makes the claim **weaker** — the antecedent fires on fewer names | `NameFreeOk` (`declaresName κ n` is a *disjunct* of the conclusion), `BareNameFree` (`defDeclared? κ.defs n = none` is an antecedent), `MissFree` (`nameFree κ "method_missing"` is an antecedent) | **up** only |
| a bigger table makes the claim **stronger** — `∀ c ∈ C` ranges over more | `ClassesOk`, `DefsOk`, and the `consts`/`privConsts` family | **down** only |

So there is no monotonicity lemma to prove in either direction: a single `StateOk` cannot be
transported across `afterStmt` at all, and strengthening `SemJudge`'s conclusion to the grown
context buys the *up* direction at the cost of the *down* one, leaving the conclusion of
`JudgeSeq.cons` unstatable.

The design that would work is visible from here and is not a lemma: `SemJudgeSeq`'s conclusion
has to be at the context after **all** of `es`, so that no step ever transports downward. That
needs a "context after a statement list" function — and `extendConsts` takes the statement's
*type*, which `SemJudgeSeq`'s signature does not carry. Hence the census's verdict: this is a
change to `Judge`'s signature, i.e. to all 178 derivations, and not something a rung can route
around.

That is the sixth stall point ("`κ` threaded through the judgment") arriving from the consumer's
end, exactly as `Denote/Sem/notes.md` says it does — and it is now the *only* thing between this
file and the rung. Recorded here rather than in a comment because the run half is proved and
reusable, and because the table above is the measurement that says which repairs are dead.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- `.seqK` is not a `catchK`. -/
theorem catchFree_seqK (rest : List RubyCore.Expr) :
    RubyCore.Proof.CatchFree [.seqK rest] := by
  intro k hk t
  rcases List.mem_singleton.mp hk with rfl
  simp

/-- `[.seqK rest]` is jump-opaque: `unwind` has no arm for it, so the default passes the jump
through with the continuation popped — and a jump at an empty continuation never returns a
value. -/
theorem jumpOpaque_seqK (rest : List RubyCore.Expr) : JumpOpaque [.seqK rest] := by
  intro m j fuel v m' h
  match fuel with
  | 0 => exact absurd h (by simp [Interp.run])
  | f + 1 =>
    rw [Interp.run] at h
    have hs : Interp.stepFn { m with ctl := .jump j, kont := [.seqK rest] }
        = .next (Interp.withCtl { m with ctl := .jump j, kont := [] } (.jump j)) := rfl
    rw [hs] at h
    exact jump_empty_never_value f _ v m' ⟨j, rfl⟩ rfl h

/-- **Delivering into the tail of a sequence.** The machine `applyKont`'s `.seqK` arm lands on
is the tail sequence's own machine — but not always *the same* machine `evalFrom` reaches:
`evalExpr`'s singleton arm (`.seq [e]`) pushes **no** continuation, while `applyKont` pushes a
trailing `.seqK []`. So the two-or-more case is one step and the one-statement case is a second
`run_split`, at `[.seqK []]`, whose delivery is a value at an empty continuation and therefore
`.done`.

Stated over the machine rather than over `deliver` so the caller can hand it the state it has. -/
theorem evals_seqK_tail {m₀ : Machine} {w : Value} {e' : Ratchet.Expr} {es : List Ratchet.Expr}
    {v : Value} {m' : Machine} {f : Nat}
    (h : Interp.run f (Interp.withKont { m₀ with ctl := .value w, kont := [] }
        (.eval (toRuby e')) (.seqK (toRubyList es))) = .value v m') :
    Evals m₀ (.seq (e' :: es)) v m' := by
  cases es with
  | cons f₁ fs =>
    -- two or more: `evalFrom` of the tail steps to exactly this machine
    refine ⟨f + 1, ?_⟩
    rw [run_succ]
    exact h
  | nil =>
    -- one: strip the trailing `.seqK []` with a second split
    have hpush : Interp.withKont { m₀ with ctl := .value w, kont := [] }
        (.eval (toRuby e')) (.seqK (toRubyList ([] : List Ratchet.Expr)))
        = pushK [.seqK []] (evalFrom m₀ e') := rfl
    rw [hpush] at h
    obtain ⟨n, v₁, m₁, hinner, hctl, hkont, f2, houter⟩ :=
      run_split [.seqK []] (catchFree_seqK []) (jumpOpaque_seqK []) f (evalFrom m₀ e') v m' h
    -- the delivery is `.value v₁` at an empty continuation: one step to `.done`
    have hm₁ : ({ m₁ with ctl := .value v₁, kont := [] } : Machine) = m₁ := by
      rw [← hctl, ← hkont]
    have hd : Interp.stepFn (deliver m₁ v₁ [.seqK []])
        = .next { m₁ with ctl := .value v₁, kont := [] } := rfl
    match f2 with
    | 0 => rw [run_zero] at houter; exact absurd houter (by simp)
    | f3 + 1 =>
      have hstep1 : Interp.run (f3 + 1) (deliver m₁ v₁ [.seqK []]) = Interp.run f3 m₁ := by
        rw [run_succ, hd, hm₁]
      rw [hstep1] at houter
      match f3 with
      | 0 => rw [run_zero] at houter; exact absurd houter (by simp)
      | f4 + 1 =>
        -- `m₁` has a value in flight and an empty continuation: `applyKont` is `.done`
        have hdone : Interp.stepFn m₁ = .done v₁ m₁ := by
          show Interp.stepFn m₁ = _
          rw [show Interp.stepFn m₁ = Interp.applyKont m₁ v₁ from by
            unfold Interp.stepFn; rw [hctl]]
          unfold Interp.applyKont
          rw [hkont]
        have hstep2 : Interp.run (f4 + 1) m₁ = Interp.RunResult.value v₁ m₁ := by
          rw [run_succ, hdone]
        rw [hstep2] at houter
        obtain ⟨rfl, rfl⟩ : v₁ = v ∧ m₁ = m' := by
          simp only [Interp.RunResult.value.injEq] at houter; exact houter
        -- and `.seq [e']` is `e'` one step later, which is `evals_seq_one`'s equation
        exact ⟨n + 1, by rw [run_succ]; exact hinner⟩

/-- **A multi-statement sequence runs its head, then the rest.** Both machines exhibited; the
middle one is the state the first statement's own run ends at, which is what `Evals` is about.

The proof is `run_split` at `[.seqK rest]` plus the two one-step equalities that identify the
pushed machine with `pushK` of `evalFrom`, and the delivery state with `evalFrom` of the tail. -/
theorem evals_seq_cons {m : Machine} {e e' : Ratchet.Expr} {es : List Ratchet.Expr}
    {v : Value} {m' : Machine} (h : Evals m (.seq (e :: e' :: es)) v m') :
    ∃ (v₀ : Value) (m₀ : Machine), Evals m e v₀ m₀ ∧ Evals m₀ (.seq (e' :: es)) v m' := by
  obtain ⟨fuel, hrun⟩ := h
  -- step 1: the `.seq` arm pushes `.seqK rest` and evaluates the head, which *is* `pushK`
  -- of the head's own `evalFrom`
  let rest : List RubyCore.Expr := toRubyList (e' :: es)
  have hstep : Interp.stepFn (evalFrom m (.seq (e :: e' :: es)))
      = .next (pushK [.seqK rest] (evalFrom m e)) := rfl
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | fuel + 1 =>
  rw [run_succ, hstep] at hrun
  obtain ⟨n, v₀, m₀, hinner, hctl, hkont, f2, houter⟩ :=
    run_split [.seqK rest] (catchFree_seqK rest) (jumpOpaque_seqK rest) fuel
      (evalFrom m e) v m' hrun
  refine ⟨v₀, m₀, ⟨n, hinner⟩, ?_⟩
  -- step 2: delivering the head's value to `.seqK rest` reaches the tail sequence's own
  -- machine — in one step when the tail has two or more statements, and in two when it has
  -- one, because `applyKont` pushes a trailing `.seqK []` where `evalExpr`'s singleton arm
  -- pushes nothing. That asymmetry is the whole of `evals_seqK_tail` below.
  match f2 with
  | 0 => rw [run_zero] at houter; exact absurd houter (by simp)
  | f3 + 1 =>
    rw [run_succ] at houter
    have hd : Interp.stepFn (deliver m₀ v₀ [.seqK rest])
        = .next (Interp.withKont { m₀ with ctl := .value v₀, kont := [] }
            (.eval (toRuby e')) (.seqK (toRubyList es))) := rfl
    rw [hd] at houter
    exact evals_seqK_tail houter

#print axioms evals_seq_cons
#print axioms jumpOpaque_seqK

end Ratchet.Denote
