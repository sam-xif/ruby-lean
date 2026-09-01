import Denote.Sem.Obligations
import Denote.Rules

/-!
# `Denote/Ladder.lean` — the semantic ratchet's number

One rung, one `Judge` rule discharged over the semantic denotation. This file computes the
count, and it computes it the only way that cannot drift: by asking the kernel.

For each of the 83 constructors of `Ratchet/Judge.lean`'s mutual family it looks for a
declaration named `Sem.<Family>.<rule>` and checks **its type is definitionally equal to
`Obl.<Family>.<rule>`** — the obligation `Denote/Sem/Obligations.lean` derived from the
constructor itself. Both halves matter:

* *Existence alone* would let a rung be claimed by a declaration of the right name and the
  wrong statement. The `isDefEq` check is what makes the ladder's number a claim about the
  rule rather than about a naming convention.
* *A hand-written checklist* would let the denominator go stale the moment a rule is added to
  `Ratchet/Judge.lean` — and a rule added without an obligation is precisely the gap this
  ladder exists to make visible. So the denominator is read out of the inductive on every
  build.

The result is baked into `semLadderRows` at elaboration time, which is what lets the plain
`semladder` executable print it without carrying a Lean environment around at runtime.

## What counts as a rung, and what a rung costs

A rung is not "a program that validates" (that is the *other* ladder, `Main.lean`, and its
number is 177 of 232). A rung here is a **rule**, and the two ladders measure different
things on purpose: the syntactic ratchet measures reach, this one measures justification. A
program can climb the first without any of the second, which is exactly the situation
`Denote/notes.md` was written to describe.

Rungs are not uniform, and the derivation makes the non-uniformity visible rather than
hiding it behind a count. `Obl.Judge.intLit` is two `stepFn` unfoldings. `Obl.Judge.prim`
quantifies over the whole `PrimSig` relation, so discharging it means justifying every row of
that table — ninety-odd separate facts about CRuby's builtins — from the semantics. Both are
one rung. The honest reading of "N of 83" is therefore *N rules justified*, not *N/83 of the
work*, and `AGENTS.md` says so where it reports the number.
-/

set_option autoImplicit false

open Lean Meta Elab Command

namespace Ratchet.Denote

/-! ## Where the command puts its answer

Two `String`s rather than a `List (String × String × Bool)`, and the reason is prosaic: a
`toExpr`-generated list-of-nested-tuples literal makes Lean's own code generator fall over
here (`unknown join point`, an IR-check panic), while a string literal compiles fine. So the
rows are emitted space-separated and split back apart at runtime. The kernel's answer is
unaffected — only the transport is. -/

/-- Single-backtick `Name`s: neither constant exists until `build_semantic_ladder` declares
it. -/
def allRulesName : Name := `Ratchet.Denote.semLadderAllRules
def doneRulesName : Name := `Ratchet.Denote.semLadderDoneRules

/-- **The check, as a function.** Returns every family rule's label, and the subset that is
discharged — i.e. for which a declaration named `Sem.<Family>.<rule>` exists *and* has a type
definitionally equal to the derived `Obl.<Family>.<rule>`.

Both conditions are the point. Existence alone would let a rung be claimed by the right name
attached to the wrong statement; `isDefEq` against the obligation is what makes the ladder's
number a claim about the rule. (`Obl.…` carries the `abbrev` reducibility hint, so `isDefEq`
unfolds it.) -/
def ladderStatus : CommandElabM (List String × List String) := do
  let env ← getEnv
  let ctors ← match familyCtors env with
    | .ok cs => pure cs
    | .error msg => throwError msg
  let mut all : List String := []
  let mut done : List String := []
  for (ind, c) in ctors do
    let label := s!"{ind.getString!}.{c.getString!}"
    all := all ++ [label]
    match env.find? (semName c) with
    | none => pure ()
    | some info =>
      if ← liftTermElabM (isDefEq info.type (Lean.mkConst (oblName c))) then
        done := done ++ [label]
  return (all, done)

/-- Bake `ladderStatus`'s answer into two `String` constants, so the plain `semladder`
executable can print the report without carrying a Lean environment at runtime.

`addAndCompile`, not `addDecl`: a declaration added without being compiled has no IR, and
every definition downstream of it then fails to compile — which is how this was found. -/
elab "build_semantic_ladder" : command => do
  let (all, done) ← ladderStatus
  let mkStr (nm : Name) (xs : List String) : CommandElabM Unit :=
    liftCoreM <| addAndCompile (.defnDecl
      { name := nm, levelParams := [], type := Lean.mkConst ``String,
        value := Lean.mkStrLit (String.intercalate " " xs),
        hints := .opaque, safety := .safe })
  mkStr allRulesName all
  mkStr doneRulesName done

/-- Log the live status without declaring anything — for exercising the gate itself, and for
use from a scratch file downstream of this one (where `build_semantic_ladder` cannot run a
second time). -/
elab "semantic_ladder_status" : command => do
  let (all, done) ← ladderStatus
  logInfo m!"discharged {done.length}/{all.length}: {done}"

build_semantic_ladder

/-! ## The report -/

/-- `"Judge.intLit"` -> `"Judge"`. -/
def famOf (label : String) : String := (label.splitOn ".").headD label

def allRules : List String := semLadderAllRules.splitOn " "

def doneRules : List String :=
  if semLadderDoneRules.isEmpty then [] else semLadderDoneRules.splitOn " "

/-- Family display order: `Judge` first (67 of the 83 rules), then the companions in the order
`Denote/Sem/Judge.lean` defines them. -/
def familyOrder : List String :=
  ["Judge", "JudgeAll", "JudgeKw", "JudgePairs", "JudgeSeq", "JudgeRescues", "JudgeConsts",
   "JudgeNested"]

/-- The rules with no discharge on file, in the inductives' own constructor order. -/
def remaining : List String := allRules.filter (fun r => !doneRules.contains r)

private def pad (s : String) (n : Nat) : String :=
  if s.length ≥ n then s else s ++ String.ofList (List.replicate (n - s.length) ' ')

def report : String :=
  let perFamily := familyOrder.filterMap fun fam =>
    let tot := (allRules.filter (fun r => famOf r == fam)).length
    let dn := (doneRules.filter (fun r => famOf r == fam)).length
    if tot == 0 then none else some s!"  {pad fam 14} {dn}/{tot}"
  let bar := "  " ++ String.ofList (List.replicate 24 '-')
  let tot := s!"  {pad "total" 14} {doneRules.length}/{allRules.length}"
  let next :=
    if remaining.isEmpty then
      ["", "Every rule is discharged -- `Denote/Adequacy.lean`'s `judge_semJudge` can close."]
    else
      ["", "next up (the inductives' own constructor order):"]
        ++ (remaining.take 8).map (fun r => s!"  {r}")
        ++ (if remaining.length > 8 then
              [s!"  ... and {remaining.length - 8} more"] else [])
  String.intercalate "\n"
    (["=== SEMANTIC RATCHET: Judge rules discharged over the semantic denotation ===", ""]
      ++ perFamily ++ [bar, tot] ++ next)

/-- Nonzero while rules remain, matching `Main.lean`'s convention for the syntactic ladder. -/
def exitCode : UInt32 := if remaining.isEmpty then 0 else 1

end Ratchet.Denote
