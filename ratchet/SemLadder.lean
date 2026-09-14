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
def safeRungFloor : Nat := 38

/-- The recorded size of the registry. **A clink once registered never unregisters**
(`ratchet/AGENTS.md`), and this number is sound to ratchet on: a clink cannot be registered
without its proof, so the count is a count of proofs. Raise it when the registry grows; a
drop means a proof was deleted or broken. -/
def clinkFloor : Nat := 16

/-- How many unmet goals the **quiet** report prints before truncating. The full list is
`--verbose`; this is the number that keeps a commit-time gate readable, since the list is 251
entries long today and a report nobody scrolls is a report nobody reads. -/
def goalLimit : Nat := 20

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
  /-- Typed **and** proved `StuckFree` end to end. The only complete state. -/
  | proved
  /-- `validateD` accepted it and every rule it needs is registered: the registry can
  justify it today and nobody has. Started and incomplete. -/
  | ready
  /-- `validateD` accepted it, so a **certificate exists** — but the derivation leans on
  rules with no semantic proof, so nothing backs that certificate end to end. Started and
  incomplete, and the rule names say what is owed. -/
  | certified (on : List String)
  /-- The checker rejects it and every rule it needs is registered: no certificate, so
  nothing is owed. (A deliberately ill-typed rung lives here.) -/
  | rejected
  /-- Not accepted, and needs a rule that is not in the judgment. Pure ascent. -/
  | blocked (on : List String)
  | outOfFragment (on : List String)
  | noProgram (why : String)

def GoalState.label : GoalState → String
  | .proved => "proved"
  | .ready => "STARTED, INCOMPLETE -- every rule registered, no safety theorem"
  | .certified on => s!"STARTED, INCOMPLETE -- certified, but {String.intercalate ", " on} \
{if on.length == 1 then "has" else "have"} no semantic proof"
  | .rejected => "rejected by the checker (no certificate, nothing owed)"
  | .blocked on => s!"blocked on {String.intercalate ", " on}"
  | .outOfFragment on => s!"outside the judgment ({String.intercalate ", " on})"
  | .noProgram why => s!"no program ({why})"

/-- The states that are **started and incomplete** -- the ones that make the ratchet RED. -/
def GoalState.isRed : GoalState → Bool
  | .ready => true
  | .certified _ => true
  | _ => false

structure Goal where
  name : String
  state : GoalState

/-- Left-justify to `w`, so the quiet list reads as two columns. -/
def pad (w : Nat) (s : String) : String :=
  if s.length >= w then s else s ++ String.ofList (List.replicate (w - s.length) ' ')

/-- Classify one built rung. `rulesUsed` is the predictor `Denote/Typed/Safety.lean` §4
describes -- and the reason it is trustworthy here is `Denote/Typed/RuleAudit.lean` §3, which
checks it against the proof terms on every rung that has one.

**`accepted` is what makes a rung "started".** `validateD` accepting a rung means a
certificate for it exists and checks; a rung is on the ladder from that moment. If no
end-to-end safety proof backs it, the rung is half-climbed -- the ladder is claiming a rung
the safety determination does not reach. Whether that is because the rules are proved and
nobody wrote the theorem (`ready`) or because the rules themselves have no semantic proof
(`certified`) changes the remedy, not the verdict. -/
def classify (name : String) (accepted : Bool) (prog : Option Ratchet.Expr) : GoalState :=
  match prog with
  | none => .noProgram "upstream stage declined"
  | some p =>
    if safeRungs.any (·.1 == name) then .proved
    else
      let used := (rulesUsed p).eraseDups
      let missing := used.filter fun r => !dRegisteredRules.contains r
      if accepted then
        if missing.isEmpty then .ready else .certified missing
      else if missing.contains "?" then .outOfFragment missing
      else if missing.isEmpty then .rejected
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
    -- The whole rung, not just its program: `Rung.verdict` is `validateD` on the pair, the
    -- same Bool `ratchetd` reports, and it is what says whether a certificate exists.
    let rung? : Option Ratchet.Rung :=
      match Json.parse contents with
      | .error _ => none
      | .ok j => (Ratchet.Rung.ofJson? j).toOption
    let prog := rung?.bind (·.program)
    let accepted := (rung?.map (·.verdict)).getD false
    goals := goals ++ [{ name, state := classify name accepted prog }]
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

/-! ## The two reports

`--quiet` (what `scripts/run_typed_ratchet.sh` runs by default) prints the **goal list and
nothing else**: the unmet rungs in corpus order, truncated at `goalLimit`, with the rolled-up
tally. Everything above it -- the registry columns, the safety banner, the per-rung
cross-check -- is narration for a reader who asked for it, and `--verbose` is where it lives.

What `--quiet` does *not* suppress is any gate firing. Every failure path below prints its own
explanation and returns non-zero in both modes; the flag chooses how much is said when
everything is fine, never how much is said when it is not. -/

def main (args : List String) : IO UInt32 := do
  let quiet := args.contains "--quiet"
  let dirArg? := (args.filter fun a => !a.startsWith "--").head?
  let dn := dRegisteredRules.length
  -- `say` is the narration; `IO.println` is a finding. The distinction is the whole flag.
  let say : String → IO Unit := fun m => unless quiet do IO.println m
  say "=== CLINK REGISTRY: rules in the certified judgment `DJudgeC dclinks` ==="
  say ""
  say s!"  DJudge   {dn} registered   {dUnregisteredRules.length} not in the judgment"
  say s!"  registered: {String.intercalate ", " dRegisteredRules}"
  say s!"  owed:       {String.intercalate ", " dUnregisteredRules} \
(`runA_pushK` is proved; see Denote/Typed/JudgeA.lean §4 for what each still needs)"
  if !dFamBlockedRules.isEmpty then
    say s!"  of those, owed TWICE: {String.intercalate ", " dFamBlockedRules} \
-- their premises reach {String.intercalate ", " dCompanionRules},"
    say "              which `DFam` carries no field for, so `register_dclink` refuses"
    say "              them before asking for a proof: the statement a proof would have"
    say "              to prove is the wrong one until the family is extended (§F31)."
  say ""
  say "Every registered rule carries its own proof (`Clink.sem`), and that proof is"
  say "TWO obligations: the answer-typed reading (hypothesis is an answer, not a value;"
  say "the conclusion says whether the run reached a type-stuck outcome) AND end-to-end"
  say "safety. So `dregistry_safe` is unconditional and holds at every registry size --"
  say "a rule cannot join without its safety proof. The right-hand column is COVERAGE,"
  say "not debt: an unregistered rule is not in the judgment at all. Which is not a reason to"
  say "leave it there -- coverage bounds what any certificate can say, so the target is 0 and"
  say "the rung tally at the bottom says which rule buys the most."
  say ""
  say "=== END-TO-END SAFETY, at the real prelude-booted machine ==="
  say s!"  {safeRungs.length} corpus rungs proved `StuckFree bootMachine <program>`, \
at every fuel:"
  say s!"    {String.intercalate ", " (safeRungs.map (·.1))}"
  say "  Each is one theorem in Denote/Typed/Safety.lean with every hypothesis"
  say "  discharged (`stateOk_boot`, conditional on the `bootOkB` build gate), and"
  say "  `#print axioms` showing only propext/Classical.choice/Quot.sound."
  say ""
  say s!"  rules exercised by those rungs: \
{String.intercalate ", " (dRegisteredRules.filter (fun r => rulesExercised.contains r))}"
  say "  (read off the proof terms, not off the programs -- Denote/Typed/RuleAudit.lean)"
  if !unexercised.isEmpty then
    say s!"  registered but NOT exercised end to end: \
{String.intercalate ", " unexercised} ({unexercised.length} of a ceiling of \
{unexercisedCeiling}) -- see found-issues.md §F30."
    say "  These are proved and in the judgment, but no rung the safety proof covers uses"
    say "  them, so the end-to-end claim is about a narrower fragment than the registry."
    say "  A non-empty list is legitimate in an intermediate state -- `var` needs a program"
    say "  that binds a local first, which needs `seq` -- but it should never be LARGE, and"
    say "  `unexercisedCeiling` only ever moves down. Growing it is the reviewable act."
  -- The cross-check, when a build directory is given.
  let mut crossOk := true
  let mut ready : List String := []
  let mut goals' : List Goal := []
  match dirArg? with
  | none =>
    say ""
    say "  (pass a build directory -- `lake exe semladder build` -- to also check each"
    say "   theorem is about the program the pipeline built for that rung, and to list"
    say "   the unmet goals in corpus order)"
  | some dir =>
    say ""
    say s!"  cross-check against {dir}:"
    for q in safeRungs do
      let r ← checkRung dir q.1 q.2
      -- A mismatch is a finding, so it is printed in both modes.
      if r.ok then say s!"    {q.1}: {r.status}"
      else
        IO.println s!"    {q.1}: {r.status}"
        crossOk := false
    -- The goal list, in corpus rung order. This is the part `--quiet` keeps.
    let goals ← loadGoals dir
    goals' := goals
    ready := goals.filterMap fun g => if g.state.isRed then some g.name else none
    let unmet := goals.filter fun g => match g.state with | .proved => false | _ => true
    IO.println ""
    -- **The ladder's reach, under the definition this report enforces**: the leading run of
    -- corpus rungs that are typed *and* proved `StuckFree`. `ratchetd`'s LADDER REACH counts
    -- the leading run the *checker* is satisfied by, which is a weaker thing and a larger
    -- number; the gap between them is exactly the RED below.
    let safetyReach := (goals.takeWhile fun g =>
      match g.state with | .proved => true | _ => false).length
    if quiet then
      IO.println s!"{goals.length} rungs · safety reach {safetyReach} · \
{goals.length - unmet.length} proved safe · {unmet.length} unmet"
      -- The two rule counts mean different things and are easy to read as one. Both carry
      -- their direction, because a bare number invites the reader to decide it is fine.
      if dUnregisteredRules.isEmpty then
        IO.println s!"  {dn} rules certified, 0 owed -- every rule in the judgment is proved"
      else
        IO.println s!"  {dn} rules certified · {dUnregisteredRules.length} OWED: \
{String.intercalate ", " dUnregisteredRules} -- no semantic proof, so nothing that needs one"
        IO.println "    can be certified. This is coverage, and the target is 0."
      if unexercised.isEmpty then
        IO.println "  0 exempt -- every certified rule is exercised by a proved rung"
      else
        IO.println s!"  {unexercised.length}/{unexercisedCeiling} certified rules EXEMPT from \
end-to-end exercise: {String.intercalate ", " unexercised} -- proved and"
        IO.println "    in the judgment, but no proved rung uses them. Only ever shrink this;"
        IO.println "    non-empty is legitimate mid-ladder, large is not (§F30)."
    else
      IO.println s!"=== SAFETY REACH: {safetyReach} rungs typed AND proved StuckFree ==="
      IO.println ""
      IO.println "  This is the ladder's reach under the definition the gate below enforces."
      IO.println "  `ratchetd`'s LADDER REACH counts the leading run the *checker* accepts,"
      IO.println "  which is a weaker claim and a larger number. A rung between the two is"
      IO.println "  certified and unproved -- started, and incomplete."
      IO.println ""
      IO.println "=== UNMET GOALS, in corpus rung order ==="
    IO.println ""
    if unmet.isEmpty then
      IO.println "  (none -- every built rung has an end-to-end safety proof)"
    else
      let shown := if quiet then unmet.take goalLimit else unmet
      for g in shown do
        IO.println s!"  {pad 44 g.name}{g.state.label}"
      if quiet && unmet.length > goalLimit then
        IO.println s!"  ... and {unmet.length - goalLimit} more \
(--verbose for the full list, and for how each number above was reached)"
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
    unless quiet do
      IO.println s!"  {goals.length} built rungs: {goals.length - unmet.length} proved, \
{unmet.length} unmet"
    if !sortedTally.isEmpty then
      IO.println s!"  blocked on: \
{String.intercalate ", " (sortedTally.map fun t => s!"{t.1} ({t.2})")}"
    say "  -- a rule with a rung count is the next unit of work; `?` is a head with no"
    say "     DJudge rule at all, so those rungs need the judgment extended first."
  -- The gates. Each prints in both modes: `--quiet` is about narration, not about findings.
  if !crossOk then
    IO.println ""
    IO.println "RATCHET RED -- a safety theorem is about a different program than its rung's."
    IO.println "  The rung is started and incomplete: the theorem is true of something, and"
    IO.println "  not of the program the pipeline built. See the MISMATCH lines above."
    return 1
  if !ready.isEmpty then
    IO.println ""
    IO.println s!"RATCHET RED -- {ready.length} rung(s) started and incomplete."
    IO.println ""
    IO.println "  `validateD` accepts each of these, so a certificate for it exists and checks."
    IO.println "  None has an end-to-end safety proof, so the ladder is claiming rungs the"
    IO.println "  safety determination does not reach. A rung is climbed when it is typed AND"
    IO.println "  proved `StuckFree` -- not when the checker alone is satisfied."
    IO.println ""
    let nowProvable := ready.filter fun n =>
      goals'.any fun g => g.name == n && (match g.state with | .ready => true | _ => false)
    let owedRules := ((goals'.filterMap fun g =>
      match g.state with | .certified on => some on | _ => none).flatten).eraseDups
    if !nowProvable.isEmpty then
      IO.println s!"  provable today ({nowProvable.length}) -- every rule registered, nobody \
wrote the theorem:"
      IO.println s!"    {String.intercalate ", " nowProvable}"
    let leaningNames := ready.filter fun n => !nowProvable.contains n
    let leaning := leaningNames.length
    if leaning > 0 then
      let shown := String.intercalate ", " (leaningNames.take 12)
      let andMore := if leaning > 12 then s!" ... and {leaning - 12} more" else ""
      IO.println s!"  certified against rules with no semantic proof ({leaning}), waiting on \
{String.intercalate ", " owedRules}:"
      IO.println s!"    {shown}{andMore}"
    IO.println ""
    IO.println "  Two ways out, and they are not equivalent: prove the rules and then the"
    IO.println "  rungs, which is the work; or lower the recorded reach so the ladder stops"
    IO.println "  claiming them, which is the honest bookkeeping if the reach was aspirational."
    return 1
  if unexercised.length > unexercisedCeiling then
    IO.println ""
    IO.println s!"RATCHET RED -- the exemption list widened: {unexercised.length} certified \
rules are exempt from end-to-end exercise, ceiling is {unexercisedCeiling}."
    IO.println "  Exempt rules are started and incomplete by construction. Non-empty is"
    IO.println "  legitimate mid-ladder; growing the list is not, unless the ceiling moves"
    IO.println "  with it and someone reviews that (§F30)."
    return 1
  if safeRungs.length < safeRungFloor then
    IO.println ""
    IO.println s!"RATCHET RED -- a recorded floor moved: {safeRungs.length} rungs proved safe, \
floor is {safeRungFloor}. A rung once climbed never un-climbs, so a proof was deleted."
    return 1
  if dn < clinkFloor then
    IO.println ""
    IO.println s!"RATCHET RED -- a recorded floor moved: {dn} rules certified, floor is \
{clinkFloor}. A clink was lost, which means a semantic proof was deleted or broken."
    return 1
  if dn > clinkFloor then
    IO.println ""
    IO.println s!"RATCHET RED -- {dn} rules certified against a floor of {clinkFloor}. This is \
progress, not damage: raise `clinkFloor` in SemLadder.lean to lock it in."
    return 1
  -- GREEN is deliberately not claimed here. This report knows its own gates passed; it does
  -- not know that the Lean build, the corpus pipeline, agreement and reach did.
  -- `scripts/run_typed_ratchet.sh` is the layer that knows, and it is the layer that says so.
  say ""
  say s!"This report's gates pass: {dn} rules certified, {safeRungs.length} rungs proved safe,"
  say "every floor held. Reach and agreement are `scripts/run_typed_ratchet.sh`'s to check,"
  say "so the overall GREEN/RED verdict is its to give, not this report's."
  return 0
