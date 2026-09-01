import Denote.Sem.Judge
import Lean.Elab.Command

/-!
# `Denote/Sem/Obligations.lean` — the 83 proof obligations, derived rather than transcribed

A rung of this ratchet is **one `Judge` rule, restated over the semantic denotation and
proved from `stepFn`**. The restating is mechanical, and doing it by hand would be 83
transcriptions of premises like `PrimSig (.arrayOf τ) "include?" [σ] .bool` — 83 chances to
weaken an obligation by a typo, in a file whose whole job is to be the thing nothing is
trusted against.

So it is not done by hand. `Ratchet.SemJudge` and friends were given **exactly** their
syntactic twins' signatures (`Denote/Sem/Judge.lean`), which makes the restating a
substitution of one constant for another inside the constructor's own type:

```
Judge.intLit  :  ∀ {κ Γ I n},  Judge κ Γ I (.int n) .int Γ I
Obl.Judge.intLit :=  ∀ {κ Γ I n},  SemJudge κ Γ I (.int n) .int Γ I
```

`deriveSemanticObligations` below does that for all 83 constructors of the eight-member
mutual family, and declares each as `Obl.<Family>.<rule> : Prop`.

## What this buys, precisely

* **The denominator is live.** It comes from `Ratchet.Judge`'s actual constructor list, read
  out of the environment. Add a rule to `Ratchet/Judge.lean` and the ratchet's total grows by
  itself; the ladder reports it as undischarged the same day. Contrast the corpus, where a
  committed snapshot is exactly right (`AGENTS.md`: "a ratchet whose number depends on a live
  sample is not a ratchet") — here the *rule set* is not a sample, it is the specification,
  and a stale copy of it would be the bug.
* **An obligation cannot be weakened.** `Denote/Ladder.lean` counts a rule as discharged only
  when a declaration named `Sem.<Family>.<rule>` exists **and its type is defeq to
  `Obl.<Family>.<rule>`**. Proving something easier and naming it after the rule does not
  count.
* **The premises stay.** Nothing substitutes `PrimSig`, `EqSafe`, `NilQSafe`, `NarrowCond`,
  `envGet?` — they are the rule's hypotheses and they belong in the obligation. Which means
  the obligation for `Judge.prim` reads "for **every** row of the `PrimSig` table, the send
  returns a value of the row's result type": one rung that owes ~90 separate facts about
  CRuby's builtins. That is not an accident of the derivation, it is what `Judge.prim` claims,
  and seeing the cost stated is the point of deriving the obligation instead of writing a
  friendlier one.

## What it does not do

It does not derive *proofs*, and it does not derive the **induction**. Adequacy —
`Judge … → SemJudge …` — is one `induction h` with one case per constructor, so it closes only
when all 83 are on file; `Denote/Adequacy.lean` states it and explains why partial credit is
not available for that particular theorem while it is available for every rung.
-/

set_option autoImplicit false

open Lean Meta Elab Command

namespace Ratchet.Denote

/-- The eight members of `Ratchet/Judge.lean`'s mutual family, each paired with the semantic
definition of the same signature. This list is the *only* hand-written part of the
derivation, and a member missing from it would show up as a `Judge` premise left mentioning
the syntactic relation — which fails to typecheck, because a `Judge …` premise inside a
`Prop` about `SemJudge` is well-formed but the resulting obligation would be provable only
from a syntactic derivation, defeating the exercise. So: eight rows, checked below to be
exactly the family. -/
def judgeFamily : List (Name × Name) :=
  [(``Ratchet.Judge, ``Ratchet.Denote.SemJudge),
   (``Ratchet.JudgeAll, ``Ratchet.Denote.SemJudgeAll),
   (``Ratchet.JudgeKw, ``Ratchet.Denote.SemJudgeKw),
   (``Ratchet.JudgePairs, ``Ratchet.Denote.SemJudgePairs),
   (``Ratchet.JudgeSeq, ``Ratchet.Denote.SemJudgeSeq),
   (``Ratchet.JudgeRescues, ``Ratchet.Denote.SemJudgeRescues),
   (``Ratchet.JudgeConsts, ``Ratchet.Denote.SemJudgeConsts),
   (``Ratchet.JudgeNested, ``Ratchet.Denote.SemJudgeNested)]

/-- `Obl.Judge.intLit` from `Ratchet.Judge.intLit`. -/
def oblName (ctor : Name) : Name :=
  match ctor with
  | .str (.str _ fam) rule => `Ratchet.Denote.Obl ++ Name.mkSimple fam ++ Name.mkSimple rule
  | _ => `Ratchet.Denote.Obl ++ ctor

/-- `Sem.Judge.intLit` — where the *discharge* for a rule must live, and under which name
`Denote/Ladder.lean` looks for it. -/
def semName (ctor : Name) : Name :=
  match ctor with
  | .str (.str _ fam) rule => `Ratchet.Denote.Sem ++ Name.mkSimple fam ++ Name.mkSimple rule
  | _ => `Ratchet.Denote.Sem ++ ctor

/-- The substitution: every occurrence of a syntactic family head becomes its semantic twin.
Everything else — `PrimSig`, `EqSafe`, `envGet?`, the `Ty` helpers — is left exactly as the
rule wrote it. -/
def substSemHeads (e : Lean.Expr) : Lean.Expr :=
  Lean.Expr.replace (fun x =>
    match x with
    | .const n _ => (judgeFamily.lookup n).map (fun n' => .const n' [])
    | _ => none) e

/-- Every constructor of the family, in the inductives' own order. -/
def familyCtors (env : Environment) : Except String (List (Name × Name)) := do
  let mut out : List (Name × Name) := []
  for (ind, _) in judgeFamily do
    match env.find? ind with
    | some (.inductInfo vi) => out := out ++ vi.ctors.map (fun c => (ind, c))
    | _ => throw s!"{ind} is not an inductive"
  return out

/-- Declare `Obl.<Family>.<rule> : Prop` for all 83 constructors. Kernel-checked on the way
in: if `SemJudge`'s signature ever stops matching `Judge`'s, this command fails rather than
producing an obligation about the wrong thing. -/
elab "derive_semantic_obligations" : command => do
  let env ← getEnv
  let ctors ← match familyCtors env with
    | .ok cs => pure cs
    | .error msg => throwError msg
  for (_, c) in ctors do
    let some (.ctorInfo ci) := env.find? c
      | throwError s!"{c} is not a constructor"
    let ty := substSemHeads ci.type
    let nm := oblName c
    liftTermElabM do
      let sort ← inferType ty
      unless (← isDefEq sort (mkSort .zero)) do
        throwError m!"obligation for {c} is not a Prop (it is a {sort})"
    liftCoreM <| addDecl (.defnDecl
      { name := nm, levelParams := [], type := mkSort .zero, value := ty,
        hints := .abbrev, safety := .safe })

derive_semantic_obligations

/-! Sanity: the derivation covered exactly the mutual family, no member forgotten. `all` on
any member of a mutual inductive lists every member, so this compares the hand-written
`judgeFamily` against the kernel's own view of it. -/

run_cmd do
  let env ← getEnv
  let some (.inductInfo vi) := env.find? ``Ratchet.Judge
    | throwError "Ratchet.Judge is not an inductive"
  let declared := judgeFamily.map (·.1)
  unless vi.all.all declared.contains && declared.all vi.all.contains do
    throwError m!"judgeFamily does not match Judge's mutual family: kernel says {vi.all}"

end Ratchet.Denote
