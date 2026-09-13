#!/usr/bin/env bash
# The **typed** ratchet: Sorbet in the loop, end to end.
#
#   corpus/NNN.rb  (annotated, the source of truth)
#     1. srb -p symbol-table   -> the signature manifest        ] untrusted
#     2. the strip stack       -> the plain program             ] untrusted
#     3. export-json           -> the AST                       ] untrusted
#     4. emit_deriv.py         -> a `Deriv`, or a named block   ] untrusted
#     5. lake exe ratchetd     -> `validateD`'s Bool            ] TRUSTED, and only this
#
# Four steps, in the order that matters:
#
#   0. **The negative controls** (`Ratchet/DerivControls.lean`, `#guard`ed at build
#      time): a checker that accepts everything would pass every rung below, so the
#      controls are checked before any count is reported.
#   1. **Stages 1-4** over every rung, into `build/`.
#   2. **Agreement** (`--sut lean`) over the *stripped* programs -- the ones the
#      certificates are about. A rung the model runs differently from CRuby is a rung
#      whose type is a statement about a fiction. Skip with RATCHET_SKIP_AGREEMENT=1.
#   3. **The report** (`lake exe ratchetd`), whose exit code is non-zero on a moved
#      Sorbet verdict, a new upstream failure, or a drop in ladder reach.
#   4. **The safety proof, cross-checked against the corpus** (`lake exe semladder build`).
#      The end-to-end theorems in `Denote/Typed/Safety.lean` name their rung in a docstring;
#      this reads the rung the pipeline actually built and compares its sig-stripped program
#      against the `Expr` each theorem is about, so "rung 004 is proved safe" cannot be true
#      of a theorem and false of the ladder. It also reports which registered rules those
#      rungs **exercise** -- read off the proof terms, not guessed from the programs
#      (`Denote/Typed/RuleAudit.lean`) -- and names the ones they do not (today: `var` and
#      `vasgn`, structurally; see `found-issues.md` §F30), and it ends with the **unmet
#      goals in corpus rung order**: every built rung that has no safety proof, with the
#      rules it is waiting on, and a tally of which missing rule blocks the most rungs.
#
#      Three ways it goes non-zero, beyond a moved floor:
#        * a safety theorem is about a different program than its rung's;
#        * a built rung uses **only registered rules** and has no safety theorem -- the
#          registry can already justify it and nothing has (`SAFETY COVERAGE REGRESSED`);
#        * the `unexercised` exemption list grew past its recorded ceiling
#          (`COVERAGE HATCH WIDENED`).
#
# `validateD` types (`Ratchet/Check.lean`); a `true` means a `DJudge` derivation exists.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
RATCHET_DIR="$PWD"

echo "=== the negative controls (#guard, at build time) ==="
lake build Ratchet.DerivControls Denote.Typed.Safety Denote.Typed.RuleAudit ratchetd semladder
echo

echo "=== stages 1-4: sorbet -> strip -> desugar -> emit ==="
python3 scripts/build_corpus.py "$@"
echo

if [[ "${RATCHET_SKIP_AGREEMENT:-0}" == "1" ]]; then
  echo "=== agreement (CRuby vs the Lean semantics): SKIPPED (RATCHET_SKIP_AGREEMENT=1)"
else
  echo "=== agreement over the sig-stripped programs (CRuby vs the Lean semantics) ==="
  ( cd ../difftest && uv run python -m difftest replay "$RATCHET_DIR/build" --sut lean )
fi
echo

echo "=== stage 5: the typed ladder ==="
.lake/build/bin/ratchetd build
echo

echo "=== the safety proof, cross-checked against the corpus -- and the unmet goals ==="
exec .lake/build/bin/semladder build
