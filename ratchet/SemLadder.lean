import Denote.Typed.Clink

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

open Ratchet.Denote.Typed

/-- The recorded size of the registry. **A clink once registered never unregisters**
(`ratchet/AGENTS.md`), and this number is sound to ratchet on: a clink cannot be registered
without its proof, so the count is a count of proofs. Raise it when the registry grows; a
drop means a proof was deleted or broken. -/
def clinkFloor : Nat := 8

def main : IO UInt32 := do
  let dn := dRegisteredRules.length
  IO.println "=== CLINK REGISTRY: rules in the certified judgment `DJudgeC dclinks` ==="
  IO.println ""
  IO.println s!"  DJudge   {dn} registered   {dUnregisteredRules.length} not in the judgment"
  IO.println s!"  registered: {String.intercalate ", " dRegisteredRules}"
  IO.println s!"  owed:       {String.intercalate ", " dUnregisteredRules} \
(all four behind `RunAPushK` -- Denote/Typed/JudgeA.lean §4)"
  IO.println ""
  IO.println "Every registered rule carries its own proof (`Clink.sem`), in the ANSWER-TYPED"
  IO.println "shape: the hypothesis is an answer rather than a value, and the conclusion says"
  IO.println "whether the run reached a type-stuck outcome. `dregistry_sound` is unconditional"
  IO.println "and holds at every registry size. The right-hand column is COVERAGE, not debt:"
  IO.println "an unregistered rule is not in the judgment at all, so nothing is owed for it"
  IO.println "and nothing unsound can be certified with it."
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
