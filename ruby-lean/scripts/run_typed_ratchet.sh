#!/usr/bin/env bash
# The active typed ratchet: GREEN means the production validateD soundness
# theorem passes for the enabled clinks, with its controls and pipeline checks.
# Disabled clinks and declined positive rungs are ascent, not proof debt.
# --full-corpus retains the historical full-coverage audit and its original floors.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
RATCHET_DIR="$PWD"
VERBOSE=0
FULL=0
REBUILD=0
PASSTHROUGH=()
OUT=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --verbose|-v) VERBOSE=1; shift ;;
    --full-corpus) FULL=1; shift ;;
    --clink-rebuild) REBUILD=1; shift ;;
    --out)
      [[ $# -gt 1 ]] || { echo "--out needs a directory" >&2; exit 2; }
      OUT="$2"; PASSTHROUGH+=("$1" "$2"); shift 2 ;;
    --out=*) OUT="${1#--out=}"; PASSTHROUGH+=("$1"); shift ;;
    --help|-h)
      echo "Usage: scripts/run_typed_ratchet.sh [--verbose] [corpus pipeline options]"
      echo "  default         Check active soundness and report enabled clinks/corpus rungs climbed."
      echo "  --clink-rebuild Check active soundness and controls without the corpus pipeline."
      echo "  --full-corpus   Run the historical complete-registry/corpus audit and floors."
      echo "  Pipeline options: [corpus-dir] [--only prefixes] [--jobs N] [--out directory]"
      echo "  RATCHET_SKIP_AGREEMENT=1 skips the CRuby replay while iterating."
      exit 0 ;;
    *) PASSTHROUGH+=("$1"); shift ;;
  esac
done
if [[ "$FULL" == 1 && "$REBUILD" == 1 ]]; then
  echo "Choose --full-corpus or --clink-rebuild" >&2; exit 2
fi
if [[ "$FULL" == 1 ]]; then
  [[ "$VERBOSE" == 1 ]] && PASSTHROUGH=(--verbose ${PASSTHROUGH[@]+"${PASSTHROUGH[@]}"})
  exec ./scripts/run_full_typed_ratchet.sh ${PASSTHROUGH[@]+"${PASSTHROUGH[@]}"}
fi
if [[ "$REBUILD" == 1 ]]; then
  [[ ${#PASSTHROUGH[@]} == 0 ]] || { echo "--clink-rebuild accepts only --verbose" >&2; exit 2; }
  if [[ "$VERBOSE" == 1 ]]; then exec ./scripts/run_clink_rebuild.sh --verbose; fi
  exec ./scripts/run_clink_rebuild.sh
fi

LOGDIR="$(mktemp -d)"
trap 'rm -rf "$LOGDIR"' EXIT
# Fresh output prevents a filtered corpus run from counting old cached rungs.
CORPUS_OUT="${OUT:-$LOGDIR/corpus}"
[[ "$CORPUS_OUT" == /* ]] || CORPUS_OUT="$RATCHET_DIR/$CORPUS_OUT"
stage() {
  local label="$1"; shift
  if [[ "$VERBOSE" == 1 ]]; then
    echo "=== $label ==="
    "$@" || { echo "RATCHET RED -- $label" >&2; exit 1; }
  elif ! "$@" >"$LOGDIR/stage.log" 2>&1; then
    echo "RATCHET RED -- $label" >&2
    if grep -qE '^error:' "$LOGDIR/stage.log"; then
      grep -E '^error:' -A 6 "$LOGDIR/stage.log" | head -60 >&2 || true
    else
      tail -40 "$LOGDIR/stage.log" >&2
    fi
    exit 1
  fi
}
CLINK_ARGS=()
[[ "$VERBOSE" == 1 ]] && CLINK_ARGS+=(--verbose)
stage "active validator soundness and controls" ./scripts/run_clink_rebuild.sh ${CLINK_ARGS[@]+"${CLINK_ARGS[@]}"}
stage "active progress report and model runner" lake build active-ratchet rubycore
stage "Sorbet -> strip -> desugar -> emit" python3 scripts/build_corpus.py \
  --out "$CORPUS_OUT" ${PASSTHROUGH[@]+"${PASSTHROUGH[@]}"}
if [[ "${RATCHET_SKIP_AGREEMENT:-0}" == 1 ]]; then
  echo "agreement: SKIPPED (RATCHET_SKIP_AGREEMENT=1)"
else
  stage "agreement: CRuby vs the Lean semantics" bash -c \
    'cd "$1/../difftest" && uv run python -m difftest replay "$2" --sut lean --out "$3"' _ "$RATCHET_DIR" "$CORPUS_OUT" "$LOGDIR/agreement"
  if [[ "$VERBOSE" == 0 ]]; then
    python3 - "$LOGDIR/agreement/summary.json" <<'PY'
import json, sys
result = json.load(open(sys.argv[1]))
print(f"agreement: {result['verdicts'].get('agree', 0)} agree, {len(result['disagreements'])} disagree")
PY
  fi
fi
REPORT_ARGS=("$CORPUS_OUT")
[[ "$VERBOSE" == 0 ]] && REPORT_ARGS+=(--quiet)
# The report is the result the user came for; always show its output.
if ! ./.lake/build/bin/active-ratchet "${REPORT_ARGS[@]}"; then
  echo "RATCHET RED -- active corpus controls" >&2; exit 1
fi
echo
echo "RATCHET GREEN -- validateD_safe_run passes for the enabled clinks."
echo "  Climbed corpus rungs are the programs validateD accepts under this registry."
