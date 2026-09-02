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
here touches the machine.

What they are not is *padding*. `JudgeAll.nil` is the statement that evaluating no arguments
leaves the machine alone and produces no values, and a `SemJudgeAll` that failed to say that
would be the wrong definition — the base case is exactly where a list relation's shape is
checked. `JudgeSeq` is the one family whose first constructor is **not** here, and the reason
is the ladder's current wall: `JudgeSeq.last` carries a `Judge` premise about a statement
that runs under a pushed `.seqK`, so it needs the continuation-decomposition lemma
(`../Sem/notes.md` §The fifth stall point) exactly as `Judge.vasgn` does.
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
  intro κ Γ I m hm vs m' h
  obtain ⟨rfl, rfl⟩ := evalsAll_nil h
  exact ⟨rfl, trivial, hm⟩

theorem Sem.JudgeKw.nil : Obl.JudgeKw.nil := by
  intro κ Γ I m hm vs m' h
  obtain ⟨rfl, rfl⟩ := evalsAll_nil (by simpa [kwExprs] using h)
  exact ⟨rfl, trivial, hm⟩

/-- The pair list's base case. `ks ++ vs = []` forces both halves empty, so the two
"every key/value is in the join" conjuncts are vacuous — which is the right reading: the join
over no pairs is `.never`, and `denM .never` is `False`, so a non-vacuous claim here would be
unprovable rather than merely weak. -/
theorem Sem.JudgePairs.nil : Obl.JudgePairs.nil := by
  intro κ Γ I m hm ks vs m' h _
  obtain ⟨hnil, rfl⟩ := evalsAll_nil (by simpa using h)
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hnil
  exact ⟨rfl, by simp, by simp, hm⟩

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
