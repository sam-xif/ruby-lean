#!/usr/bin/env bash
# The semantics bootstraptest ratchet.
#
# The Lean model is replayed against MRI's `bootstraptest` corpus (the tier-0
# differential run) and this compares the run's `summary.json` against a
# checked-in high-watermark. Three things can only ever go one way:
#
#   agree             higher is better  -> watermark is a MINIMUM
#   sut_unsupported   lower  is better  -> watermark is a MAXIMUM
#   disagree          must stay 0       -> a hard zero, not a watermark
#
# A fall is RED. A rise is progress: the script prints the new number and asks
# the author to raise the watermark in the same PR (it does not write it — the
# only way a watermark changes is a reviewed commit, per issue #4).
#
#   scripts/ci/check_semantics_watermark.sh REPORT_DIR
#   scripts/ci/check_semantics_watermark.sh --save REPORT_DIR
#
# REPORT_DIR is a `uv run python -m difftest run --tier 0 --sut lean` output
# directory containing summary.json. With --save, write the run's numbers as
# the new baseline (a deliberate human act, exactly like `bin/coverage --save`).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
BASELINE="$ROOT/difftest/coverage-baseline.json"

SAVE=0
if [[ "${1:-}" == "--save" ]]; then SAVE=1; shift; fi
REPORT="${1:-}"
if [[ -z "$REPORT" || ! -f "$REPORT/summary.json" ]]; then
  echo "usage: $0 [--save] REPORT_DIR   (REPORT_DIR must contain summary.json)" >&2
  exit 2
fi

python3 - "$BASELINE" "$REPORT/summary.json" "$SAVE" <<'PY'
import json
import sys

baseline_path, summary_path, save = sys.argv[1], sys.argv[2], sys.argv[3] == "1"

base = json.load(open(baseline_path))
summary = json.load(open(summary_path))

v = summary.get("verdicts", {})
ran = int(summary.get("total", 0))
agree = int(v.get("agree", 0))
unsupported = int(v.get("sut_unsupported", 0))
disagree = int(v.get("disagree", 0))

if save:
    new = {
        "corpus": base.get("corpus", "bootstraptest"),
        "ran": ran,
        "agree": agree,
        "sut_unsupported": unsupported,
        "disagree": disagree,
    }
    with open(baseline_path, "w") as fh:
        json.dump(new, fh, indent=2)
        fh.write("\n")
    print(f"baseline saved: {new}")
    raise SystemExit(0)

print("semantics bootstraptest ratchet")
print(f"  corpus           {summary.get('sut', '?')}")
print(f"  ran              {ran}")
print(f"  agree            {agree}   (watermark >= {base['agree']})")
print(f"  sut_unsupported  {unsupported}   (watermark <= {base['sut_unsupported']})")
print(f"  disagree         {disagree}   (must be 0)")

regressions = []
if disagree > 0:
    regressions.append(f"disagree {disagree} > 0")
if agree < base["agree"]:
    regressions.append(f"agree {agree} < watermark {base['agree']} (-{base['agree'] - agree})")
if unsupported > base["sut_unsupported"]:
    regressions.append(
        f"sut_unsupported {unsupported} > watermark {base['sut_unsupported']} "
        f"(+{unsupported - base['sut_unsupported']})"
    )

if ran != base.get("ran"):
    print(
        f"\nNOTE: the corpus size moved ({base.get('ran')} -> {ran}); the harvested "
        f"bootstraptest set changed, so move `ran` in the baseline in this same PR."
    )

if regressions:
    print()
    for r in regressions:
        print(f"RATCHET REGRESSION -- semantics/bootstraptest: {r}")
    raise SystemExit(1)

rises = []
if agree > base["agree"]:
    rises.append(f"agree {base['agree']} -> {agree}")
if unsupported < base["sut_unsupported"]:
    rises.append(f"sut_unsupported {base['sut_unsupported']} -> {unsupported}")

if rises:
    print()
    print("RATCHET ADVANCED -- semantics/bootstraptest: " + ", ".join(rises))
    print("  This is progress, not damage. Raise the watermark in")
    print("  difftest/coverage-baseline.json in this PR to lock it in.")
else:
    print("\nRATCHET OK -- semantics/bootstraptest holds its watermark.")
PY
