#!/usr/bin/env bash
# Two steps, in the order that matters:
#
#   1. **Agreement** (`scripts/run_agreement.sh`): every rung's `.rb` run under
#      CRuby and under the Lean semantics, observations compared. This runs
#      first because it is what makes a rung's *type* mean anything -- typing a
#      program the model executes differently from Ruby is typing a fiction.
#      Any disagreement aborts before the ladder is even reported. Skip with
#      RATCHET_SKIP_AGREEMENT=1 (see that script for when that is reasonable).
#   2. **The ladder**: `validate`'s verdict per rung against the corpus's
#      recorded target, plus the tier summary. One number per tier, all of it
#      synthesized -- there are no certificates and nothing is trusted (see
#      Main.lean's docstring). Exit code is nonzero while any rung's actual
#      verdict differs from its target, which today is most rungs above tier 2:
#      the climb, not a bug.
#
# `scripts/run_check13.sh` is the third piece: the evidence behind the rungs the
# hand-authored judgment (`Ratchet/Judge.lean`) actually covers.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

if [[ "${RATCHET_SKIP_AGREEMENT:-0}" == "1" ]]; then
  echo "=== corpus agreement (CRuby vs the Lean semantics): SKIPPED (RATCHET_SKIP_AGREEMENT=1)"
else
  echo "=== corpus agreement (CRuby vs the Lean semantics) ==="
  scripts/run_agreement.sh
  echo
fi

echo "=== the ladder (validate vs each rung's target) ==="
lake build
exec .lake/build/bin/ratchet corpus
