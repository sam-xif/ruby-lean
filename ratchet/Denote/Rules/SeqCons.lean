import Denote.Rules.Seq
import Denote.Sem.Decompose
import Denote.Sem.Down

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

**Closed 2026-09-10.** `Sem.JudgeSeq.cons` is at the bottom of this file, axiom-clean. What
follows is the account of the transport, kept because two of the three things L268 recorded
here turned out to be wrong and the corrections are the content.

`Obl.JudgeSeq.cons`'s second premise is at context `κ.afterStmt e σ` while its conclusion is at
`κ`, so the rung needs `StateOk` moved **both ways** across `afterStmt`. L268 measured that
neither direction held, on two families with opposite variance. Both were removed, by different
pieces of `context-splitting.md`, and neither by a monotonicity lemma:

**Up — gone, because the components moved to `Neg`.** L268's "up only" column was
`NameFreeOk`/`BareNameFree`/`MissFree`, each of which read a *positive* table negatively
(`declaresName κ n`, `defDeclared? κ.defs n = none`, `nameFree κ "method_missing"`). Step 1's
whole-program seed (§F20) put all three — and `MethodsExact`, and then `BaseChainsOk`'s three
guards — onto `Neg`, which `Ctx.afterStmt` does not touch. They are **invariant**, so the column
is empty. And step 4 made `SemJudge` claim outgoing conformance at the context a statement
*reports* as well as the one it started from, so premise 1 hands premise 2 exactly the
`StateOk (κ.afterStmt e σ) Γ₁ I₁ m₁` it wants: nothing is transported up, it is stated.

**Down — proved, but not as §3 priced it.** `Denote/Sem/Down.lean` is the transport, and it
splits three ways rather than being "antitone, one line":

* **Free** — `ClassesOk`, `DefsOk`, and the membership halves of `NestedClassesOk`/`DeclClassOk`
  really are `∀ x ∈ table` claims over a table that *grows*: `mergeCls` **prepends** the merged
  entry rather than replacing it in place, and `extendDefs`/`addPrivNames` cons.
* **Invariant** — everything reading `κ.neg` or `κ.scope`, which is most of `StateOk`, since
  `Ctx.afterStmt` rewrites only `pos`. Those are the same proposition at both contexts.
* **Owed** — `ConstsOk`/`ConstPathsOk`, because `extendConsts` is `envSet` and **overwrites**;
  and `DeclClassOk`'s four guarded clauses, whose antecedents fire on fewer inputs as the table
  grows. `Ratchet.ctxKept` is the decidable premise that buys exactly these, it is
  `JudgeSeq.cons`'s third, and every one of the 178 hand derivations discharges it by `rfl`.

So the "design that would work" this file used to describe — `SemJudgeSeq` concluding after
*all* of `es` — was not needed, and the census's verdict that this is "a change to `Judge`'s
signature, i.e. to all 178 derivations" was right about the change and wrong about the cost: the
signature changed, and no derivation term moved (`Judge.out_afterStmt`).

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

/-! ## The rung

Everything above is the *run* half. This is the rest, and it is short because the two halves of
the transport that L268 could not have were each removed by a different piece of
`context-splitting.md`:

* **up** — premise 1's second outgoing conjunct *is* `StateOk (κ.afterStmt e σ) Γ₁ I₁ m₁`, which
  is exactly premise 2's input. Nothing is transported; `SemJudge` states it
  (`Denote/Sem/Judge.lean` §Outgoing conformance). That is step 4.
* **down** — `StateOk_afterStmt_down` (`Denote/Sem/Down.lean`), which the rule's third premise
  `ctxKept` buys. That is §F21's residue, made checkable.

`Framed` composes by `trans`, and the plainness conjunct is the two premises'. -/

theorem Sem.JudgeSeq.cons : Obl.JudgeSeq.cons := by
  intro κ κ₁ Γ Γ₁ Γ₂ I I₁ I₂ e e' es σ τ hhead htail hkept
  refine ⟨fun x hx => ?_, ?_⟩
  · -- plainness: the head's is its own premise, the tail's is the tail's
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hhead.1
    · exact htail.1 x hx
  intro m hm v m' hev
  -- **the run splits**, and both machines are exhibited
  obtain ⟨v₀, m₀, hin, hout⟩ := evals_seq_cons hev
  -- **premise 1** at the head's own run. Its *second* outgoing conjunct is the one premise 2
  -- wants: conformance at the context the statement reports, not at the one it started from.
  obtain ⟨hf₁, _, _, hok₁⟩ := hhead.2 m hm v₀ m₀ hin
  -- **premise 2** consumes it directly — this is the step L268 measured as impossible
  obtain ⟨hf₂, hden, hok₂⟩ := htail.2 m₀ hok₁ v m' hout
  -- **the conclusion** is at `κ`, and `ctxKept` is what carries the tail's conformance back
  -- down the declaration the head performed.
  exact ⟨hf₁.trans hf₂, hden, StateOk_afterStmt_down hkept hok₂⟩

#print axioms evals_seq_cons
#print axioms jumpOpaque_seqK
#print axioms Sem.JudgeSeq.cons

end Ratchet.Denote
