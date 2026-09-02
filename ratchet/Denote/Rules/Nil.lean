import Denote.Rules.Core
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Nil.lean` — the base case of each companion family

`Judge` is one member of an eight-member mutual family, and the other seven have their own
constructor orders. Six of them start at a **base case** — the empty argument list, the empty
keyword list, the empty pair list, the empty rescue list, the empty constant list, the empty
nesting list — and each of those is discharged here.

**These are cheap, and saying so is part of the measurement.** The ladder's own report says
"a rung is one rule, not one unit of work"; this file is the sharp end of that. Four of the
six are *vacuous* — a `∀ x ∈ [], …` — and the other two (`JudgeAll.nil`, `JudgeKw.nil`) come
down to `EvalsAll m [] vs m'` forcing `vs = []` and `m' = m` by its own definition. Nothing
here touches the machine. (Since clink 53 the last conjunct is `DenAllAt m [] [] [] m'`, which
is *that same* `m' = m` rather than a `True` — the seventh stall point's fix made the base case
say the one thing it should.)

What they are not is *padding*. `JudgeAll.nil` is the statement that evaluating no arguments
leaves the machine alone and produces no values, and a `SemJudgeAll` that failed to say that
would be the wrong definition — the base case is exactly where a list relation's shape is
checked. `JudgeSeq` is the one family whose first constructor is **not** here, because it has
no empty case at all: its base is the *singleton* sequence, which is `Denote/Rules/Seq.lean`
and a different argument (`evalExpr` pushes no continuation for a one-statement `seq`).

This paragraph previously said `JudgeSeq.last` was behind the continuation wall
(`../Sem/notes.md` §The fifth stall point). That was wrong, and wrong in the direction that
costs a rung: the wall is real for `JudgeSeq.cons`, whose first statement runs under a pushed
`.seqK`, and `evalExpr`'s `[e]` arm pushes nothing. Corrected in clink 48, which climbed it.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The two that read `EvalsAll` -/

/-- Evaluating no expressions consumes no values and moves nothing. -/
theorem evalsAll_nil {m m' : Machine} {vs : List Value} (h : EvalsAll m [] vs m') :
    vs = [] ∧ m' = m := by
  cases vs with
  | nil => exact ⟨rfl, h⟩
  | cons v vs => exact absurd h (by simp [EvalsAll])

theorem Sem.JudgeAll.nil : Obl.JudgeAll.nil := by
  intro κ Γ I
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm vs m' h
  obtain ⟨rfl, rfl⟩ := evalsAll_nil h
  exact ⟨rfl, rfl, hm⟩

theorem Sem.JudgeKw.nil : Obl.JudgeKw.nil := by
  intro κ Γ I
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm vs m' h
  obtain ⟨rfl, rfl⟩ := evalsAll_nil (by simpa [kwExprs] using h)
  exact ⟨rfl, rfl, hm⟩

/-- The pair list's base case. Since clink 53 this is `JudgeAll.nil`'s shape exactly — the
interleaved reading (`pairExprs []`) makes the empty pair list the empty expression list, and
`DenPairsAt m [] kr vr [] m'` is `m' = m`. The old statement had to split a `ks ++ vs = []`
because the halves were concatenated; that concatenation is what the seventh stall point's
second defect was. -/
theorem Sem.JudgePairs.nil : Obl.JudgePairs.nil := by
  intro κ Γ I
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm vals m' h
  obtain ⟨rfl, rfl⟩ := evalsAll_nil (by simpa [pairExprs] using h)
  exact ⟨rfl, rfl, hm⟩

/-! ## The four that are vacuous -/

theorem Sem.JudgeRescues.nil : Obl.JudgeRescues.nil := by
  intro κ Γ I cls binding handler hmem
  exact absurd hmem (by simp)

theorem Sem.JudgeConsts.nil : Obl.JudgeConsts.nil := by
  intro κ n e hmem
  exact absurd hmem (by simp)

theorem Sem.JudgeNested.nil : Obl.JudgeNested.nil := by
  intro κ pfx isMod n body hmem
  exact absurd hmem (by simp)

#print axioms Sem.JudgeAll.nil
#print axioms Sem.JudgeKw.nil
#print axioms Sem.JudgePairs.nil
#print axioms Sem.JudgeRescues.nil
#print axioms Sem.JudgeConsts.nil
#print axioms Sem.JudgeNested.nil

end Ratchet.Denote
