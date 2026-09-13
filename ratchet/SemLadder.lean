import Denote.Typed.RuleAudit
import Ratchet.Rung

/-!
# `semladder` — the clink registry's report

Two ratchets run in this package and neither substitutes for the other:

* **`ratchet`/`ratchetd`** — *reach*: how many corpus programs the checker types.
* **`semladder`** — the **certified judgment**: which of `Ratchet/Judge.lean`'s rules are in
  `JudgeC clinks`, i.e. which have a semantic proof attached as a `Clink.sem` field.

**What changed, 2026-09-11.** This used to print *48 of 83 rules discharged* — a numerator of
proofs over a denominator of rules authored, with the gap standing for debt on rules that were
already in the judgment and already reachable by a certificate. That number is gone, and so is
the debt reading, because the judgment is now generated from the registry
(`Denote/Clink/Spec.lean`): a rule with no proof is not an undischarged obligation, it is not a
rule. `registry_sound` is unconditional and was unconditional at registry size 1; there is no
83/83 to reach and no terminal induction to take.

So this report has two columns and only one of them is about us:

* **registered** — rules in the certified judgment. Each carries its own proof; the count can
  only fall by someone deleting one, which is what `clinkFloor` below watches.
* **not in the judgment** — coverage. What `JudgeC` cannot type yet, which bounds what a
  certificate can be checked against, and is the thing to reduce.

Exit code is the ratchet: non-zero if the registry has **shrunk** below the recorded floor.
Not "non-zero while rules remain" — under the old framing that was a permanent red light,
which is a light nobody reads.

Four other ways it goes red, each a way the ladder could claim more (or less) than it has:

* a safety theorem is about a different program than the rung it names (the cross-check);
* a built rung uses **only registered rules** and has no safety theorem — the registry can
  already justify it and nobody did (`SAFETY COVERAGE REGRESSED`, and see the goal list);
* the `unexercised` exemption list grew past `unexercisedCeiling` (`COVERAGE HATCH WIDENED`);
* a rung count or the registry size fell below its floor.

And it ends with the **unmet goals in corpus rung order** — what is left, in the order the
corpus is written, with the rule each rung is waiting on.
-/

open Ratchet
open Ratchet.Denote.Typed
open Lean (Json)

/-- The recorded number of corpus rungs with an **end-to-end safety proof** at the real
prelude-booted machine (`Denote/Typed/Safety.lean`). This is the number the ladder exists to
grow: `StuckFree bootMachine <program>`, at every fuel, with every hypothesis discharged. A
drop means a theorem was deleted. -/
def safeRungFloor : Nat := 8

/-- The recorded size of the registry. **A clink once registered never unregisters**
(`ratchet/AGENTS.md`), and this number is sound to ratchet on: a clink cannot be registered
without its proof, so the count is a count of proofs. Raise it when the registry grows; a
drop means a proof was deleted or broken. -/
def clinkFloor : Nat := 9

/-! ## The cross-check: the safety proof is about the **corpus's own** programs

`Denote/Typed/Safety.lean`'s theorems name their rung in a docstring — `corpus/004-str-lit.rb`
— and until now that was prose. This reads the rung the pipeline actually built and compares
its **sig-stripped program** against the `Expr` the theorem is about. A theorem proved about
`.str "hello"` while `corpus/004-str-lit.rb` says something else is the one way the safety
number could be honest per-theorem and wrong per-ladder.

Reported per rung and non-zero on any mismatch, so `scripts/run_typed_ratchet.sh` can gate on
it next to reach and agreement. -/

structure RungCheck where
  name : String
  status : String
  ok : Bool

/-! ## The unmet goals, in corpus rung order

The ladder's two numbers say what is *done*. This says what is not, per rung, in the order
the corpus is written, which is the order the work happens in.

A built rung falls into one of four states:

* **proved** — it has an end-to-end safety theorem (`safeRungs`).
* **READY** — every rule its program needs is registered, so the registry can already justify
  it, and nothing has. This is a **gate**, not a report: it is the exact shape of drift the
  ladder is vulnerable to, because `safeRungs` is hand-written while the registry grows on its
  own. Register `seq` and a pile of corpus rungs become provable in one commit; without this
  check, none of them would be asked for. Non-zero.
* **blocked** — its program needs a rule that is not in the judgment. Reported with the rules
  it is waiting on, which is what turns "35 rungs unproved" into a work queue.
* **out of the fragment** — `rulesUsed` reaches a head with no rule at all (`?`).

Only `READY` is red. The rest is the goal list. -/

inductive GoalState where
  | proved
  | ready
  | blocked (on : List String)
  | outOfFragment (on : List String)
  | noProgram (why : String)

def GoalState.label : GoalState → String
  | .proved => "proved"
  | .ready => "READY -- every rule registered, no safety theorem"
  | .blocked on => s!"blocked on {String.intercalate ", " on}"
  | .outOfFragment on => s!"outside the judgment ({String.intercalate ", " on})"
  | .noProgram why => s!"no program ({why})"

structure Goal where
  name : String
  state : GoalState

/-- Classify one built rung. `rulesUsed` is the predictor `Denote/Typed/Safety.lean` §4
describes -- and the reason it is trustworthy here is `Denote/Typed/RuleAudit.lean` §3, which
checks it against the proof terms on every rung that has one. -/
def classify (name : String) (prog : Option Ratchet.Expr) : GoalState :=
  match prog with
  | none => .noProgram "upstream stage declined"
  | some p =>
    if safeRungs.any (·.1 == name) then .proved
    else
      let used := (rulesUsed p).eraseDups
      let missing := used.filter fun r => !dRegisteredRules.contains r
      if missing.contains "?" then .outOfFragment missing
      else if missing.isEmpty then .ready
      else .blocked missing

/-- Every built rung, in corpus order (the filenames are `NNN-name.rung.json`, so sorting
the paths *is* the corpus ordering). -/
def loadGoals (dir : System.FilePath) : IO (List Goal) := do
  let entries ← dir.readDir
  let files := (entries.map (·.path)).toList.filter (·.toString.endsWith ".rung.json")
  let sorted := files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  let mut goals : List Goal := []
  for f in sorted do
    let name := (f.fileName.getD "?").replace ".rung.json" ""
    let contents ← IO.FS.readFile f
    let prog : Option Ratchet.Expr :=
      match Json.parse contents with
      | .error _ => none
      | .ok j => match j.getObjVal? "program" with
        | .error _ => none
        | .ok pj => (Decode.program pj).toOption
    goals := goals ++ [{ name, state := classify name prog }]
  return goals

def checkRung (dir : System.FilePath) (name : String) (p : Ratchet.Expr) : IO RungCheck := do
  let path := dir / (name ++ ".rung.json")
  if !(← path.pathExists) then
    return { name, status := "NO BUILT RUNG (run scripts/build_corpus.py)", ok := false }
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | .error e => return { name, status := s!"unparseable: {e}", ok := false }
  | .ok j =>
    match j.getObjVal? "program" with
    | .error _ => return { name, status := "rung has no `program` (upstream stage failed)", ok := false }
    | .ok pj =>
      match Decode.program pj with
      | .error e => return { name, status := s!"undecodable: {e}", ok := false }
      | .ok prog =>
        if prog == p then return { name, status := "matches the corpus program", ok := true }
        else return { name, status := "MISMATCH: the theorem is about a different program",
                      ok := false }

def main (args : List String) : IO UInt32 := do
  let dn := dRegisteredRules.length
  IO.println "=== CLINK REGISTRY: rules in the certified judgment `DJudgeC dclinks` ==="
  IO.println ""
  IO.println s!"  DJudge   {dn} registered   {dUnregisteredRules.length} not in the judgment"
  IO.println s!"  registered: {String.intercalate ", " dRegisteredRules}"
  IO.println s!"  owed:       {String.intercalate ", " dUnregisteredRules} \
(`runA_pushK` is proved; see Denote/Typed/JudgeA.lean §4 for what each still needs)"
  if !dFamBlockedRules.isEmpty then
    IO.println s!"  of those, owed TWICE: {String.intercalate ", " dFamBlockedRules} \
-- their premises reach {String.intercalate ", " dCompanionRules},"
    IO.println "              which `DFam` carries no field for, so `register_dclink` refuses"
    IO.println "              them before asking for a proof: the statement a proof would have"
    IO.println "              to prove is the wrong one until the family is extended (§F31)."
  IO.println ""
  IO.println "Every registered rule carries its own proof (`Clink.sem`), and that proof is"
  IO.println "TWO obligations: the answer-typed reading (hypothesis is an answer, not a value;"
  IO.println "the conclusion says whether the run reached a type-stuck outcome) AND end-to-end"
  IO.println "safety. So `dregistry_safe` is unconditional and holds at every registry size --"
  IO.println "a rule cannot join without its safety proof. The right-hand column is COVERAGE,"
  IO.println "not debt: an unregistered rule is not in the judgment at all."
  IO.println ""
  IO.println "=== END-TO-END SAFETY, at the real prelude-booted machine ==="
  IO.println s!"  {safeRungs.length} corpus rungs proved `StuckFree bootMachine <program>`, \
at every fuel:"
  IO.println s!"    {String.intercalate ", " (safeRungs.map (·.1))}"
  IO.println "  Each is one theorem in Denote/Typed/Safety.lean with every hypothesis"
  IO.println "  discharged (`stateOk_boot`, conditional on the `bootOkB` build gate), and"
  IO.println "  `#print axioms` showing only propext/Classical.choice/Quot.sound."
  IO.println ""
  IO.println s!"  rules exercised by those rungs: \
{String.intercalate ", " (dRegisteredRules.filter (fun r => rulesExercised.contains r))}"
  IO.println "  (read off the proof terms, not off the programs -- Denote/Typed/RuleAudit.lean)"
  if !unexercised.isEmpty then
    IO.println s!"  registered but NOT exercised end to end: \
{String.intercalate ", " unexercised} ({unexercised.length} of a ceiling of \
{unexercisedCeiling}) -- see found-issues.md §F30"
  -- The cross-check, when a build directory is given.
  let mut crossOk := true
  let mut ready : List String := []
  match args.head? with
  | none =>
    IO.println ""
    IO.println "  (pass a build directory -- `lake exe semladder build` -- to also check each"
    IO.println "   theorem is about the program the pipeline built for that rung, and to list"
    IO.println "   the unmet goals in corpus order)"
  | some dir =>
    IO.println ""
    IO.println s!"  cross-check against {dir}:"
    for q in safeRungs do
      let r ← checkRung dir q.1 q.2
      IO.println s!"    {q.1}: {r.status}"
      if !r.ok then crossOk := false
    -- The goal list, in corpus rung order.
    let goals ← loadGoals dir
    ready := goals.filterMap fun g => match g.state with | .ready => some g.name | _ => none
    let unmet := goals.filter fun g => match g.state with | .proved => false | _ => true
    IO.println ""
    IO.println "=== UNMET GOALS, in corpus rung order ==="
    IO.println ""
    if unmet.isEmpty then
      IO.println "  (none -- every built rung has an end-to-end safety proof)"
    else
      for g in unmet do
        IO.println s!"  {g.name}  --  {g.state.label}"
    IO.println ""
    -- The work queue, rolled up: which missing rule blocks the most rungs.
    let blocking := (goals.flatMap fun g => match g.state with
      | .blocked on => on
      | .outOfFragment on => on
      | _ => []).eraseDups
    let tally := blocking.map fun r =>
      (r, (goals.filter fun g => match g.state with
            | .blocked on => on.contains r
            | .outOfFragment on => on.contains r
            | _ => false).length)
    let sortedTally := tally.toArray.qsort (fun a b => a.2 > b.2) |>.toList
    IO.println s!"  {goals.length} built rungs: {goals.length - unmet.length} proved, \
{unmet.length} unmet"
    if !sortedTally.isEmpty then
      IO.println s!"  blocked on: \
{String.intercalate ", " (sortedTally.map fun t => s!"{t.1} ({t.2})")}"
    IO.println "  -- a rule with a rung count is the next unit of work; `?` is a head with no"
    IO.println "     DJudge rule at all, so those rungs need the judgment extended first."
  if !crossOk then
    IO.println ""
    IO.println "SAFETY CROSS-CHECK FAILED: a safety theorem is not about its rung's program"
    return 1
  if !ready.isEmpty then
    IO.println ""
    IO.println s!"SAFETY COVERAGE REGRESSED: {ready.length} built rung(s) use only registered \
rules and have no safety theorem:"
    IO.println s!"    {String.intercalate ", " ready}"
    IO.println "  The registry can already justify these. Prove them in Denote/Typed/Safety.lean"
    IO.println "  and add them to `safeRungs`, or the ladder claims less than it has earned."
    return 1
  if unexercised.length > unexercisedCeiling then
    IO.println ""
    IO.println s!"COVERAGE HATCH WIDENED: {unexercised.length} registered rules are exempt \
from end-to-end exercise, ceiling is {unexercisedCeiling}"
    return 1
  if safeRungs.length < safeRungFloor then
    IO.println s!"SAFETY RATCHET REGRESSED: {safeRungs.length} rungs proved safe, \
floor is {safeRungFloor}"
    return 1
  if dn < clinkFloor then
    IO.println s!"CLINK RATCHET REGRESSED: {dn} registered, floor is {clinkFloor} \
-- a clink was lost, which means a semantic proof was deleted or broken"
    return 1
  if dn > clinkFloor then
    IO.println s!"CLINK RATCHET: {dn} registered, floor is {clinkFloor} \
-- raise `clinkFloor` in SemLadder.lean to lock it in"
    return 0
  IO.println s!"CLINK RATCHET OK ({dn} registered, all proved by construction; \
{dUnregisteredRules.length} rules not in the judgment -- that is coverage, not debt)"
  return 0
