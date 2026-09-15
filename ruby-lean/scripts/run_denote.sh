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
#   2. The clink registry. `semladder` reports which of `Ratchet/Judge.lean`'s rules are in
#      the **certified judgment** `JudgeC clinks` -- i.e. which carry a semantic proof as a
#      `Clink.sem` field. Two columns, and only the left one is about us: *registered* rules
#      are each proved by construction (`registry_sound` is unconditional and was
#      unconditional at registry size 1), and the right column is **coverage** -- rules the
#      certified judgment cannot type, which is what bounds the checker, not a debt owed.
#      Both columns are read out of the `Judge` inductive and the environment on every build,
#      so neither can go stale.
#
# The growth gate lives in the build, not here: `Denote/Clink/Registry.lean` fails to
# elaborate if a `Judge` constructor appears that is neither registered nor a named legacy
# exception, and `register_clink` refuses a rule with no proof. So "a rule and its semantic
# justification are authored together" is enforced by `lake build`, and step 1 above is where
# it fires.
#
# Exits nonzero only if the registry has **shrunk** below `SemLadder.lean`'s recorded floor.
# Parallel to `run_ratchet.sh`, not a replacement: that one measures reach over the corpus,
# this one measures what the judgment is allowed to contain.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo "--- denotation gate (Denote/Examples.lean's #guards, elaborated) ---"
lake build Denote
echo
echo "--- denotation vs. the real semantics ---"
lake exe denotereport
echo
# `semladder` needs the built rung directory; without it every rung reads as uncertified
lake exe semladder build
