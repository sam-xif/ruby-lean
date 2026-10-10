#!/usr/bin/env bash
# Check the type checker's soundness theorem and measure the checker on the corpus.
#
#   scripts/check-soundness.sh                 # everything below
#   scripts/check-soundness.sh --proofs-only   # stages 1-3: no Ruby, Sorbet or CRuby needed
#   scripts/check-soundness.sh --verbose       # every stage's full output
#   scripts/check-soundness.sh --only 001,014  # only these corpus programs
#   scripts/check-soundness.sh --record        # write corpus/accepted.txt from this run
#
# Stages, in order. The first failure stops the run and prints the captured error.
#
#   1. The checker imports nothing from the model, and its generated sources are fresh.
#   2. The soundness theorem builds for every typing rule the checker has, and depends
#      on no axiom beyond propext, Classical.choice and Quot.sound.
#   3. The negative controls build: programs and derivations the checker must refuse.
#   4. Every program in corpus/ goes through Sorbet, the desugarer and the derivation
#      emitter (scripts/build_corpus.py), and so do the pipeline's own controls
#      (scripts/check_pipeline.py).
#   5. The same programs run under CRuby and under the model; any disagreement fails.
#   6. The report: which typing rules are proved, and which corpus programs the real
#      `validateD` accepts. It fails if a program that must be rejected is accepted,
#      or if the accepted programs are not exactly those in corpus/accepted.txt.
#
# The last line is `SOUNDNESS CHECK PASSED` or `SOUNDNESS CHECK FAILED -- <stage>`.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
BOOKS="$PWD"

VERBOSE=0
PROOFS_ONLY=0
RECORD=0
OUT=""
PIPELINE_ARGS=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --verbose|-v) VERBOSE=1; shift ;;
    --proofs-only) PROOFS_ONLY=1; shift ;;
    --record) RECORD=1; shift ;;
    --out)
      [[ $# -gt 1 ]] || { echo "--out needs a directory" >&2; exit 2; }
      OUT="$2"; shift 2 ;;
    --out=*) OUT="${1#--out=}"; shift ;;
    --help|-h) sed -n '2,25p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) PIPELINE_ARGS+=("$1"); shift ;;
  esac
done
if [[ "$PROOFS_ONLY" == 1 && ( ${#PIPELINE_ARGS[@]} -gt 0 || -n "$OUT" ) ]]; then
  echo "--proofs-only takes no corpus options" >&2; exit 2
fi

LOGDIR="$(mktemp -d)"
trap 'rm -rf "$LOGDIR"' EXIT

# Run one stage. Quiet unless it fails; on failure show Lean's errors if there
# are any, the tail of the log otherwise.
stage() {
  local label="$1"; shift
  if [[ "$VERBOSE" == 1 ]]; then
    echo "=== $label ==="
    "$@" || { echo "SOUNDNESS CHECK FAILED -- $label" >&2; exit 1; }
  elif ! "$@" >"$LOGDIR/stage.log" 2>&1; then
    echo "SOUNDNESS CHECK FAILED -- $label" >&2
    if grep -qE '^error:' "$LOGDIR/stage.log"; then
      grep -E '^error:' -A 6 "$LOGDIR/stage.log" | head -60 >&2 || true
    else
      tail -40 "$LOGDIR/stage.log" >&2
    fi
    exit 1
  fi
}

# 1.
stage "the checker is isolated from the model" scripts/check-isolation.sh
stage "the checker's generated sources are fresh" \
  python3 scripts/generate_audited_checker.py --check

# 2. The registry first, so a rule without a proof is reported as that and not
#    as a failure somewhere downstream of it.
stage "the rule registry" lake build Books.TypeSoundness.Registry.GateStatus \
  Books.TypeSoundness.Registry.GateControls
stage "the soundness theorem and its axioms" lake build Books.TypeSoundness.Registry.SoundnessAudit

# 3. The whole book, which includes every control under Controls/.
stage "the checker's own controls" lake build Books.TypeSoundness.Checker.Controls.ClinkPolicyControls
stage "the type-soundness book and its controls" lake build TypeSoundness
stage "the checker executables" lake build validate-one
stage "the axiom audit of the supporting lemmas" lake env lean scripts/probes/clink-rebuild.lean

if [[ "$PROOFS_ONLY" == 1 ]]; then
  echo "SOUNDNESS CHECK PASSED (proofs only; the corpus was not run)"
  exit 0
fi

# 4. A fresh output directory, so a filtered run cannot count stale results.
CORPUS_OUT="${OUT:-$LOGDIR/corpus}"
[[ "$CORPUS_OUT" == /* ]] || CORPUS_OUT="$BOOKS/$CORPUS_OUT"
stage "the report and the model executable" lake build corpus-report rubycore
stage "the corpus pipeline: Sorbet, strip, desugar, emit" python3 scripts/build_corpus.py \
  --out "$CORPUS_OUT" ${PIPELINE_ARGS[@]+"${PIPELINE_ARGS[@]}"}
stage "the pipeline controls" python3 scripts/check_pipeline.py

# 5.
stage "agreement: CRuby and the model on the corpus" bash -c \
  'cd "$1/../difftest" && uv run python -m difftest replay "$2" --sut lean --out "$3"' \
  _ "$BOOKS" "$CORPUS_OUT" "$LOGDIR/agreement"
if [[ "$VERBOSE" == 0 ]]; then
  python3 - "$LOGDIR/agreement/summary.json" <<'PY'
import json, sys
result = json.load(open(sys.argv[1]))
print(f"model vs CRuby on the corpus: {result['verdicts'].get('agree', 0)} agree, "
      f"{len(result['disagreements'])} disagree")
PY
fi

# 6. The report is the result; always show it.
REPORT_ARGS=("$CORPUS_OUT")
[[ "$VERBOSE" == 0 ]] && REPORT_ARGS+=(--quiet)
if [[ "$RECORD" == 1 ]]; then REPORT_ARGS+=(--record corpus/accepted.txt)
else REPORT_ARGS+=(--accepted corpus/accepted.txt); fi
if ! ./.lake/build/bin/corpus-report "${REPORT_ARGS[@]}"; then
  echo "SOUNDNESS CHECK FAILED -- the corpus report" >&2; exit 1
fi
echo
echo "SOUNDNESS CHECK PASSED"
