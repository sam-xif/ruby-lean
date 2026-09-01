import Denote.Ladder

/-!
# `Denote/Adequacy.lean` — the endpoint the ladder is climbing toward

**Adequacy**: every syntactic derivation is semantically true. Eight statements, one per
member of `Ratchet/Judge.lean`'s mutual family:

```
Judge κ Γ I e τ Γ' I'  →  SemJudge κ Γ I e τ Γ' I'
```

and the seven companions likewise. `AdequacyTarget` below is that conjunction, written out.
It is not proved, and this file explains exactly what is missing and why the missing part is
all-or-nothing when every individual rung is not.

## Why the ratchet ratchets but this theorem does not

Adequacy is one **mutual induction over the derivation**, so its proof has one case per
constructor and there are 83 constructors. An induction with 80 cases filled in proves
nothing — there is no partial credit in a `Judge.rec` application. Meanwhile each individual
case *is* independent: `Obl.Judge.intLit` is a statement about `stepFn` and integer literals
that can be proved today, in isolation, and stays proved.

So the work decomposes even though the theorem does not, and the ladder measures the
decomposition:

* **`Obl.<Family>.<rule>`** (`Denote/Sem/Obligations.lean`, derived from the inductive) is one
  rung. Provable alone, and a rung once climbed never un-climbs.
* **`AdequacyHyps`** is the conjunction of all 83, generated below by folding over the same
  constructor list. It becomes provable precisely when the ladder reads 83/83 — at which point
  it is `⟨Sem.Judge.intLit, Sem.Judge.fltLit, …⟩`.
* **`AdequacyHyps → AdequacyTarget`** is the terminal clink: the mutual induction, whose every
  case is one projection out of the hypothesis. It is the only step in this ladder that cannot
  be taken early, and it is deliberately the *last* one rather than the first — writing it
  first would mean writing 83 `sorry`s, and this package has none.

That is the honest shape of the thing, and it is worth contrasting with the syntactic
ratchet's number (177 of 232 rungs, `Main.lean`): there, each rung is a *program* and the
ladder's total is a coverage measure. Here each rung is a *rule* and the total is a
justification measure. A program can climb the first ladder with none of the second done —
which is the situation `Denote/notes.md` was written to describe, and this ladder is the
answer to it.

## What a rung actually costs, stated once

Rungs are wildly non-uniform and the derivation makes that visible instead of averaging it
away. `Obl.Judge.intLit` is two `stepFn` unfoldings. `Obl.Judge.prim` quantifies over the
whole `PrimSig` relation, so climbing it means justifying every row of that table — ninety-odd
separate facts about CRuby's builtins — from the semantics. Both count as one. "N of 83"
therefore reads *N rules justified*, never *N/83 of the work*, and the ladder's own report
says so.

## The other axis, and why it is not here

`SemJudge` is partial correctness about **values**: a run that returns lands in the type's
denotation. It says nothing about runs that *don't* return, and in particular nothing about
reaching a type-stuck outcome — the `NoMethodError`/`ArgumentError`/`TypeError` family
`../type-safety-by-reachability.md` is about. `Denote/Sem/State.lean`'s `StuckFree` states
that axis; `StuckFreeTarget` below states its adequacy counterpart. Neither is on the ladder:
a rung that had to prove value-typing *and* stuck-freedom would be two rungs wearing one
number, and the two proofs have genuinely different shapes (one is about the value at a
`.value` outcome, the other is about every outcome). Kept side by side so the second axis has
a name before anyone needs it.
-/

set_option autoImplicit false

open Lean Meta Elab Command

namespace Ratchet.Denote

/-- **Adequacy of the syntactic judgment**: every `Judge` derivation, and every derivation in
each of the seven companion relations, is semantically true.

Not proved — see the module docstring. Written out by hand rather than derived, because unlike
the 83 obligations this is eight statements and reading them is the point. -/
def AdequacyTarget : Prop :=
  (∀ κ Γ I e τ Γ' I', Judge κ Γ I e τ Γ' I' → SemJudge κ Γ I e τ Γ' I') ∧
  (∀ κ Γ I es τs Γ' I', JudgeAll κ Γ I es τs Γ' I' → SemJudgeAll κ Γ I es τs Γ' I') ∧
  (∀ κ Γ I es kws Γ' I', JudgeKw κ Γ I es kws Γ' I' → SemJudgeKw κ Γ I es kws Γ' I') ∧
  (∀ κ Γ I ps kr vr Γ' I',
      JudgePairs κ Γ I ps kr vr Γ' I' → SemJudgePairs κ Γ I ps kr vr Γ' I') ∧
  (∀ κ Γ I es τ Γ' I', JudgeSeq κ Γ I es τ Γ' I' → SemJudgeSeq κ Γ I es τ Γ' I') ∧
  (∀ κ Γ I rs τ, JudgeRescues κ Γ I rs τ → SemJudgeRescues κ Γ I rs τ) ∧
  (∀ κ cs, JudgeConsts κ cs → SemJudgeConsts κ cs) ∧
  (∀ κ pfx nst, JudgeNested κ pfx nst → SemJudgeNested κ pfx nst)

/-- The second axis's counterpart, stated and off the ladder (see the module docstring):
a well-typed expression never reaches a type-stuck outcome. Not implied by `AdequacyTarget` —
`SemJudge` quantifies only over runs that produced a value. -/
def StuckFreeTarget : Prop :=
  ∀ κ Γ I e τ Γ' I', Judge κ Γ I e τ Γ' I' →
    ∀ m, StateOk κ Γ I m → StuckFree m e

/-- Where the generated conjunction of all 83 obligations lives. Single-backtick: it does not
exist until the command below declares it. -/
def adequacyHypsName : Name := `Ratchet.Denote.AdequacyHyps

/-- Declare `AdequacyHyps : Prop` — the conjunction of every derived obligation, folded over
the *same* constructor list the obligations and the ladder come from, so the three can never
disagree about what "all of them" means.

It becomes provable exactly when the ladder reads 83/83, and its proof at that point is one
anonymous-constructor term. -/
elab "derive_adequacy_hyps" : command => do
  let env ← getEnv
  let ctors ← match familyCtors env with
    | .ok cs => pure cs
    | .error msg => throwError msg
  let obls := ctors.map (fun (_, c) => Lean.mkConst (oblName c))
  let body ← match obls.reverse with
    | [] => throwError "no obligations to conjoin"
    | last :: rest => pure (rest.foldl (fun acc o => mkAnd o acc) last)
  liftTermElabM do
    let sort ← inferType body
    unless (← isDefEq sort (mkSort .zero)) do
      throwError m!"AdequacyHyps is not a Prop (it is a {sort})"
  liftCoreM <| addDecl (.defnDecl
    { name := adequacyHypsName, levelParams := [], type := mkSort .zero, value := body,
      hints := .abbrev, safety := .safe })

derive_adequacy_hyps

end Ratchet.Denote
