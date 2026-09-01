#!/usr/bin/env bash
# The **semantic ratchet**: how many of `Ratchet/Judge.lean`'s rules have been discharged as
# a proof obligation over the semantic denotation of types, proved from the real `stepFn`.
#
# Two legs, in order:
#
#   1. The denotation's own gate. `Denote/Examples.lean` is a file of `#guard`s, each of which
#      runs a real program under the real `stepFn` from the real prelude-booted heap and asks
#      `denB`/`closB`/`arrowCheck` about the value it produced -- so *elaborating* the library
#      is the check, and `lake build` fails if the denotation and the semantics disagree.
#      Elaborating it also (a) derives the 83 proof obligations from the `Judge` inductive
#      itself and (b) prints every proof file's `#print axioms` bill.
#   2. The ladder. `semladder` reports discharged/total per family, and the next rules up.
#      The denominator comes from `Judge`'s actual constructor list, so a rule added to the
#      checker shows up here as undischarged the same day; the numerator counts only
#      declarations whose *type is definitionally the derived obligation*, so a rung cannot be
#      claimed by naming something easier after the rule.
#
# Exits nonzero while rules remain, matching `run_ratchet.sh`. Parallel to that script, not a
# replacement: `run_ratchet.sh` measures reach (177 of 232 corpus rungs), this measures
# justification (0 of 83 rules). See `AGENTS.md` Semantic ratchet status.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo "--- denotation gate (Denote/Examples.lean's #guards, elaborated) ---"
lake build Denote
echo
echo "--- denotation vs. the real semantics ---"
lake exe denotereport
echo
lake exe semladder
