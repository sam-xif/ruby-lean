import Denote.Typed.RuleAudit
import Denote.Typed.Bridge
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
def safeRungFloor : Nat := 49

/-- The recorded size of the registry. **A clink once registered never unregisters**
(`ratchet/AGENTS.md`), and this number is sound to ratchet on: a clink cannot be registered
without its proof, so the count is a count of proofs. Raise it when the registry grows; a
drop means a proof was deleted or broken. -/
def clinkFloor : Nat := 48

/-- The recorded size of **the certified fragment**: corpus rungs `validateD` accepts, each
safe by `validateD_safe_boot` (`Denote/Typed/Bridge.lean`). This is the number the ladder
exists to grow, and the one that means "climbed" now that acceptance and safety are the same
fact. It only ever rises: a rung the checker accepted once is a rung it should still accept,
so a drop is a rule weakened or a corpus rung changed. -/
def fragmentFloor : Nat := 63

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
  /-- `validateD` accepts a certificate for it, so `validateD_safe_boot` proves it
  `StuckFree bootMachine` — no per-rung theorem required. **In the fragment.** -/
  | inFragment
  /-- The checker rejects it: no certificate, so nothing is claimed and nothing is owed.
  A deliberately ill-typed rung lives here, and so does one whose `sig`s `Ty` cannot say. -/
  | rejected (why : String)
  /-- The judgment has no rule for something in it, so the checker cannot even try. This is
  the ascent: the fragment grows by giving `DJudge` a rule, proving it, and registering it. -/
  | outside (why : String)
  | noProgram (why : String)

def GoalState.label : GoalState → String
  | .inFragment => "in the fragment -- safe by validateD_safe_boot"
  | .rejected why => s!"rejected by the checker ({why})"
  | .outside why => s!"outside the judgment -- {why}"
  | .noProgram why => s!"no program ({why})"

/-- Is this rung inside the certified fragment? -/
def GoalState.inFrag : GoalState → Bool
  | .inFragment => true
  | _ => false

structure Goal where
  name : String
  state : GoalState

/-- Left-justify to `w`, so the quiet list reads as two columns. -/
def pad (w : Nat) (s : String) : String :=
  if s.length >= w then s else s ++ String.ofList (List.replicate (w - s.length) ' ')

/-! ### Classifying a rung, after the bridge

Before `Denote/Typed/Bridge.lean` this function asked "does a *per-rung safety theorem* exist
for it", and a rung the checker accepted without one was `STARTED, INCOMPLETE` (§F32). That
question is now answered once, for every rung at once, by

    validateD_safe_boot : validateD p d = true → bootOkB = true → StuckFree bootMachine p

so acceptance **is** the safety proof and the half-climbed state cannot occur. What is left to
ask of a rung is only whether it is in the fragment, and if not, why — which is the work queue
for making the fragment bigger.

The one thing that could reopen the gap is the bridge ceasing to cover the judgment: a rule
added to `DJudge` without a clink. That is a whole-registry fact, not a per-rung one, so it is
gated once in `main` rather than tested here. -/
def classify (accepted expectValidate : Bool) (falseReason : Option String)
    (stage : Ratchet.RungStage) (prog : Option Ratchet.Expr) : GoalState :=
  if accepted then .inFragment
  else match stage, prog with
    | .failed st why, _ => .noProgram s!"{st}: {why}"
    | .blocked why, _ => .outside why
    | .ok, none => .noProgram "no program"
    | .ok, some _ =>
      -- The emitter produced a certificate and `validateD` said no. Whether that is correct
      -- depends on what the rung is *for*, which `expect_validate` records: a negative rung
      -- is doing its job, a positive one is a checker gap and `ratchetd` gates reach on it.
      if expectValidate then .outside "expected to type, and the checker declines it"
      else .rejected (falseReason.getD "ill-typed on purpose")

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
    let stage := (rung?.map (·.stage)).getD (.failed "load" "unreadable rung.json")
    let expectV := (rung?.map (·.expectValidate)).getD false
    let falseWhy := rung?.bind (·.falseReason)
    goals := goals ++
      [{ name, state := classify accepted expectV falseWhy stage prog }]
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
  let mut fragment : Nat := 0
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
    let frag := goals.filter (·.state.inFrag)
    let outside := goals.filter fun g => !g.state.inFrag
    fragment := frag.length
    -- **The fragment's reach**: the leading run of corpus rungs inside it. One number now,
    -- not two -- `ratchetd`'s LADDER REACH and this used to differ by the rungs that were
    -- certified and unproved (§F32), and the bridge closed that gap by construction.
    let fragReach := (goals.takeWhile (·.state.inFrag)).length
    IO.println ""
    if quiet then
      IO.println s!"{goals.length} rungs · fragment {frag.length} (reach {fragReach}) · \
{outside.length} outside"
      IO.println s!"  {dn} rules certified, {dUnregisteredRules.length} owed -- \
every rule in the judgment is proved, so `djudge_certified` covers the whole"
      IO.println "    judgment and `validateD` accepting a rung IS that rung's safety proof"
      IO.println s!"    (Denote/Typed/Bridge.lean). {safeRungs.length} rungs additionally have \
a worked theorem, cross-checked."
      if !unexercised.isEmpty then
        IO.println s!"  {unexercised.length}/{unexercisedCeiling} certified rules EXEMPT from \
end-to-end exercise: {String.intercalate ", " unexercised} (§F30)."
    else
      IO.println s!"=== THE CERTIFIED FRAGMENT: {frag.length} rungs, reach {fragReach} ==="
      IO.println ""
      IO.println "  A rung is in the fragment when `validateD` accepts a certificate for it."
      IO.println "  That is the whole safety claim, by one theorem over all of them:"
      IO.println ""
      IO.println "    validateD_safe_boot : validateD p d = true → bootOkB = true →"
      IO.println "                          StuckFree bootMachine p"
      IO.println ""
      IO.println "  composed in Denote/Typed/Bridge.lean from `validateD_typed` (the checker"
      IO.println "  returns a DJudge derivation), `djudge_certified` (the bridge: every"
      IO.println "  syntactic derivation is a certified one, because every rule has a clink)"
      IO.println "  and `dregistry_safe`. So there is no per-rung obligation left to owe, and"
      IO.println "  no gap between what the checker accepts and what is proved safe."
      IO.println ""
      IO.println s!"  {safeRungs.length} rungs additionally carry a worked theorem in"
      IO.println "  Denote/Typed/CorpusSafety.lean, cross-checked against the corpus above."
      IO.println "  Those are examples and regression, no longer the coverage story."
      IO.println ""
      IO.println "=== OUTSIDE THE FRAGMENT, in corpus rung order ==="
      IO.println "  (the ascent: each needs the judgment extended, then proved, then"
      IO.println "   registered -- at which point the bridge carries it in automatically)"
    IO.println ""
    if outside.isEmpty then
      IO.println "  (none -- every built rung is inside the certified fragment)"
    else
      let shown := if quiet then outside.take goalLimit else outside
      for g in shown do
        IO.println s!"  {pad 44 g.name}{g.state.label}"
      if quiet && outside.length > goalLimit then
        IO.println s!"  ... and {outside.length - goalLimit} more \
(--verbose for the full list, and for how each number above was reached)"
    IO.println ""
    -- The work queue, rolled up: what the *pipeline* says it hit, counted.
    let reasons := (outside.filterMap fun g =>
      match g.state with
      | .outside why => some why
      | _ => none).eraseDups
    let tally := reasons.map fun r =>
      (r, (outside.filter fun g =>
            match g.state with | .outside why => why == r | _ => false).length)
    let sortedTally := tally.toArray.qsort (fun a b => a.2 > b.2) |>.toList
    unless quiet do
      IO.println s!"  {goals.length} built rungs: {frag.length} in the fragment, \
{outside.length} outside"
    if !sortedTally.isEmpty then
      IO.println "  what the emitter hit, counted -- the fragment grows by clearing these:"
      for t in sortedTally.take 6 do
        IO.println s!"    {pad 6 s!"{t.2}x"}{t.1}"
  -- The gates. Each prints in both modes: `--quiet` is about narration, not about findings.
  if !crossOk then
    IO.println ""
    IO.println "RATCHET RED -- a worked theorem is about a different program than its rung's."
    IO.println "  The rung is started and incomplete: the theorem is true of something, and"
    IO.println "  not of the program the pipeline built. See the MISMATCH lines above."
    return 1
  -- **The bridge's side condition, as a runtime gate.** `djudge_certified` only typechecks
  -- while every `DJudge` rule has a clink, so this cannot be false in a tree that builds --
  -- `Clink.lean`'s `#guard` and the bridge itself both stop it first. It is checked anyway
  -- because it is the hypothesis the fragment's whole safety claim rests on, and a report
  -- that asserts the claim without testing its premise is a report that will one day be
  -- wrong quietly. Defence in depth, and it costs one comparison.
  if !dUnregisteredRules.isEmpty then
    IO.println ""
    IO.println s!"RATCHET RED -- the bridge no longer covers the judgment: \
{dUnregisteredRules.length} rule(s) have no semantic proof"
    IO.println s!"    {String.intercalate ", " dUnregisteredRules}"
    IO.println "  `validateD` accepts programs those rules derive, and `validateD_safe_boot`"
    IO.println "  cannot speak for them, so the fragment is claiming rungs it cannot back."
    IO.println "  Prove them (Denote/Typed/JudgeA.lean) and register them, or remove the rule."
    return 1
  if unexercised.length > unexercisedCeiling then
    IO.println ""
    IO.println s!"RATCHET RED -- the exemption list widened: {unexercised.length} certified \
rules are exempt from end-to-end exercise, ceiling is {unexercisedCeiling}."
    IO.println "  Only ever shrink this; non-empty is legitimate mid-ladder (§F30)."
    return 1
  if fragment < fragmentFloor then
    IO.println ""
    IO.println s!"RATCHET RED -- the fragment shrank: {fragment} rungs certified, floor is \
{fragmentFloor}."
    IO.println "  The fragment only ever grows -- a rung the checker accepted once is a rung"
    IO.println "  it should still accept. A rule was weakened, or a corpus rung changed."
    return 1
  if safeRungs.length < safeRungFloor then
    IO.println ""
    IO.println s!"RATCHET RED -- a recorded floor moved: {safeRungs.length} worked theorems, \
floor is {safeRungFloor}. One was deleted."
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
  if fragment > fragmentFloor then
    IO.println ""
    IO.println s!"RATCHET RED -- the fragment grew to {fragment} against a floor of \
{fragmentFloor}. This is the ladder ascending: raise `fragmentFloor` to lock it in."
    return 1
  -- GREEN is deliberately not claimed here. This report knows its own gates passed; it does
  -- not know that the Lean build, the corpus pipeline, agreement and reach did.
  -- `scripts/run_typed_ratchet.sh` is the layer that knows, and it is the layer that says so.
  say ""
  say s!"This report's gates pass: {dn} rules certified, {fragment} rungs in the fragment,"
  say "every floor held. Reach and agreement are `scripts/run_typed_ratchet.sh`'s to check,"
  say "so the overall GREEN/RED verdict is its to give, not this report's."
  return 0
