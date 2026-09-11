#!/usr/bin/env bash
# Three steps, in the order that matters:
#
#   1. **Agreement** (`scripts/run_agreement.sh`): every rung's `.rb` run under
#      CRuby and under the Lean semantics, observations compared. This runs
#      first because it is what makes a rung's *type* mean anything -- typing a
#      program the model executes differently from Ruby is typing a fiction.
#      Any disagreement aborts before the ladder is even reported. Skip with
#      RATCHET_SKIP_AGREEMENT=1 (see that script for when that is reasonable).
#   2. **The evidence** (`scripts/run_check_rungs.sh`, inlined): each climbed
#      rung's hand-authored `Judge` derivation checked against the corpus syntax
#      and against what the real semantics computes, plus the `PrimSig` negative
#      controls -- so one command covers everything.
#   3. **The ladder**: `validate`'s verdict per rung against the corpus's
#      recorded target, plus the tier summary. One number per tier, all of it
#      synthesized -- there are no certificates and nothing is trusted (see
#      Main.lean's docstring). Exit code is nonzero while any rung's actual
#      verdict differs from its target, which today is most rungs above tier 2:
#      the climb, not a bug.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

if [[ "${RATCHET_SKIP_AGREEMENT:-0}" == "1" ]]; then
  echo "=== corpus agreement (CRuby vs the Lean semantics): SKIPPED (RATCHET_SKIP_AGREEMENT=1)"
else
  echo "=== corpus agreement (CRuby vs the Lean semantics) ==="
  scripts/run_agreement.sh
  echo
fi

echo "=== the evidence behind the climbed rungs (hand derivations vs corpus + semantics) ==="
lake build ratchet checkrungs
.lake/build/bin/checkrungs corpus-untyped
echo

echo "=== the ladder (validate vs each rung's target) ==="
exec .lake/build/bin/ratchet corpus-untyped
