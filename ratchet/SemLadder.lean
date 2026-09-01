import Denote.Ladder

/-!
# `semladder` — the semantic ratchet's report

A second ratchet, running parallel to `ratchet` (`Main.lean`). The two measure different
things and neither substitutes for the other:

* **`ratchet`** — *reach*: how many corpus programs `validate` types. 177 of 232 rungs.
* **`semladder`** — *justification*: how many of `Ratchet/Judge.lean`'s rules have been
  discharged as a proof obligation over the semantic denotation of types, from `stepFn`.

The denominator is read out of the `Judge` inductive on every build and the numerator counts
only declarations whose type is definitionally the derived obligation — see
`Denote/Ladder.lean` for both mechanisms. A separate executable from `ratchet` and
`checkrungs` for the same reason those two are separate: each headline number stays a
statement about exactly one thing.

Exits nonzero while rules remain, matching `Main.lean`'s convention.
-/

def main : IO UInt32 := do
  IO.println Ratchet.Denote.report
  IO.println ""
  if Ratchet.Denote.remaining.isEmpty then
    IO.println "SEMANTIC RATCHET OK"
  else
    IO.println s!"SEMANTIC RATCHET: {Ratchet.Denote.remaining.length} rules remaining \
(a rung is one rule, not one unit of work -- see Denote/Adequacy.lean)"
  return Ratchet.Denote.exitCode
