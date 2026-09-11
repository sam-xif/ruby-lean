import Denote.Typed.Safety
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
def clinkFloor : Nat := 8

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
(all four behind `RunAPushK` -- Denote/Typed/JudgeA.lean §4)"
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
  if !unexercised.isEmpty then
    IO.println s!"  registered but NOT exercised end to end: \
{String.intercalate ", " unexercised} -- see found-issues.md §F30"
  -- The cross-check, when a build directory is given.
  let mut crossOk := true
  match args.head? with
  | none =>
    IO.println ""
    IO.println "  (pass a build directory -- `lake exe semladder build` -- to also check each"
    IO.println "   theorem is about the program the pipeline built for that rung)"
  | some dir =>
    IO.println ""
    IO.println s!"  cross-check against {dir}:"
    for q in safeRungs do
      let r ← checkRung dir q.1 q.2
      IO.println s!"    {q.1}: {r.status}"
      if !r.ok then crossOk := false
  if !crossOk then
    IO.println "SAFETY CROSS-CHECK FAILED: a safety theorem is not about its rung's program"
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
