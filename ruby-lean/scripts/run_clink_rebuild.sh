#!/usr/bin/env bash
# Check only the source-controlled active clink registry during semantic rebuilding.
# This does not certify the full checker or reset any production ratchet floor.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
verbose=0
case "${1:-}" in
  --verbose|-v) verbose=1 ;;
  --help|-h)
    echo "Usage: scripts/run_clink_rebuild.sh [--verbose]"
    echo "Select rules in Ratchet/ClinkPolicy.lean and providers in ActiveProofs.lean."
    exit 0 ;;
  "") ;;
  *) echo "Unknown argument: $1" >&2; exit 2 ;;
esac
if [[ $# -gt 1 ]]; then echo "Too many arguments" >&2; exit 2; fi
logdir="$(mktemp -d)"
trap 'rm -rf "$logdir"' EXIT
check() {
  local label="$1"; shift
  if ! "$@" >"$logdir/stage.log" 2>&1; then
    echo "CLINK REBUILD RED -- $label" >&2
    if grep -q '^error:' "$logdir/stage.log"; then
      grep '^error:' -A 6 "$logdir/stage.log" | head -60 >&2 || true
    else
      tail -40 "$logdir/stage.log" >&2
    fi
    exit 1
  fi
  if [[ "$verbose" == 1 ]]; then cat "$logdir/stage.log"; fi
}
check isolation ./scripts/check-isolation.sh
check "generated checker freshness" python3 scripts/generate_audited_checker.py --check
check "profile and registration controls" lake build Denote.Clink.GateStatus Denote.Clink.GateControls
check "actual validator controls" lake build Ratchet.Controls.ClinkPolicyControls
check "active semantic proofs and validator bridge" lake build Denote.Clink.SoundnessAudit
check "method-boundary controls" lake build Denote.Controls.MethodAliasControls Denote.Controls.MethodCodeControls Denote.Controls.FrozenDefinitionControls Denote.Controls.MethodDefinitionControls Denote.Controls.MethodOriginControls
check "actual validator executables" lake build ratchetd validate-one
check "model safety and axiom audit" lake env lean scripts/probes/clink-rebuild.lean
if [[ "$verbose" == 0 ]]; then cat "$logdir/stage.log"; fi
echo "CLINK REBUILD CHECKS PASS -- the active registry is checked; full typed ratchet remains separate."
