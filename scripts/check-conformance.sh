#!/usr/bin/env bash
# Compare a run of the model against CRuby with the recorded baseline.
#
#   scripts/check-conformance.sh REPORT_DIR          # what `make conformance` runs
#   scripts/check-conformance.sh --save REPORT_DIR   # record this run as the new baseline
#   scripts/check-conformance.sh --check-corpus [DIR] # fail fast if the baseline is stale
#
# REPORT_DIR is the output of `difftest run --tier 0 --sut lean`: the model and
# CRuby over every program of MRI's bootstraptest. Its summary.json is compared
# with difftest/coverage-baseline.json, and each number may only move one way:
#
#   ran               must equal the baseline: the corpus is harvested from a
#                     pinned CRuby tag (RUBY_REF in the Makefile), so it is fixed
#   disagree          must be 0
#   agree             may not fall below the baseline
#   sut_unsupported   may not rise above the baseline
#   not_compared      may not rise above the baseline
#
# A program is "unsupported" when the model declines it because it uses
# something the model does not cover. It is "not compared" when CRuby itself
# gives nothing to compare with: a few bootstraptest programs are deliberate
# syntax errors. When a change improves the numbers, this prints the new ones,
# annotates the CI run, and writes the GitHub step summary; commit them with
# --save in the same change.
#
# --check-corpus is the cheap half: it compares the harvested corpus with the
# baseline's `ran` without replaying either side, so `make conformance` reports
# a harvest/gating change before spending the minutes a replay takes.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${CONFORMANCE_BASELINE:-$ROOT/difftest/coverage-baseline.json}"
DEFAULT_CORPUS="$ROOT/desugar/corpus/bootstraptest"

if [[ "${1:-}" == "--check-corpus" ]]; then
  shift
  CORPUS="${1:-$DEFAULT_CORPUS}"
  python3 - "$BASELINE" "$CORPUS" <<'PY'
import json
import os
import sys
from pathlib import Path

baseline_path, corpus_path = sys.argv[1], sys.argv[2]
base = json.load(open(baseline_path))
corpus = Path(corpus_path)

if not corpus.is_dir():
    message = f"no harvested corpus at {corpus}: make conformance harvests it from the pinned CRuby tag"
    print(f"CORPUS CHECK FAILED -- {message}")
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print(f"::error title=Conformance corpus is missing::{message}")
    raise SystemExit(2)

cases = sorted(corpus.glob("*.rb"))
ran = len(cases)
recorded = int(base["ran"])
problems = []
if ran != recorded:
    problems.append(
        f"the harvested corpus has {ran} programs but the baseline records {recorded}")
accounted = (
    int(base["agree"])
    + int(base["sut_unsupported"])
    + int(base.get("not_compared", recorded - base["agree"] - base["sut_unsupported"]))
    + int(base["disagree"])
)
if accounted != recorded:
    problems.append(
        f"the baseline's counts sum to {accounted}, not its ran={recorded}")

manifest_path = corpus / "manifest.json"
if manifest_path.exists():
    manifest = json.loads(manifest_path.read_text())
    if len(manifest) != ran:
        problems.append(
            f"the corpus holds {ran} programs but its manifest lists {len(manifest)}")

if problems:
    print()
    for problem in problems:
        print(f"CORPUS CHECK FAILED -- {problem}")
    print(
        "  The baseline and the harvested corpus disagree; re-measure and record it "
        "with: make conformance && scripts/check-conformance.sh --save .make/conformance")
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print(f"::error title=Conformance baseline is stale::{'; '.join(problems)}")
    raise SystemExit(1)

print(f"CORPUS OK -- {ran} programs, and the baseline accounts for all of them")
PY
  exit $?
fi

SAVE=0
if [[ "${1:-}" == "--save" ]]; then SAVE=1; shift; fi
REPORT="${1:-}"
if [[ -z "$REPORT" || ! -f "$REPORT/summary.json" ]]; then
  echo "usage: $0 [--save] REPORT_DIR   (REPORT_DIR must contain summary.json)" >&2
  exit 2
fi

python3 - "$BASELINE" "$REPORT/summary.json" "$SAVE" "$REPORT" <<'PY'
import json
import os
import sys

baseline_path, summary_path, save, report = sys.argv[1], sys.argv[2], sys.argv[3] == "1", sys.argv[4]

base = json.load(open(baseline_path))
summary = json.load(open(summary_path))

v = summary.get("verdicts", {})
ran = int(summary.get("total", 0))
agree = int(v.get("agree", 0))
unsupported = int(v.get("sut_unsupported", 0))
disagree = int(v.get("disagree", 0))
not_compared = ran - agree - unsupported - disagree

if save:
    if disagree:
        raise SystemExit(f"not saved: {disagree} programs disagree, and a baseline never records a disagreement")
    new = {
        "corpus": base.get("corpus", "bootstraptest"),
        "ran": ran,
        "agree": agree,
        "sut_unsupported": unsupported,
        "not_compared": not_compared,
        "disagree": 0,
    }
    with open(baseline_path, "w") as fh:
        json.dump(new, fh, indent=2)
        fh.write("\n")
    print(f"baseline saved: {new}")
    raise SystemExit(0)

base_other = base.get("not_compared", base["ran"] - base["agree"] - base["sut_unsupported"])
print("model vs CRuby over bootstraptest")
print(f"  ran              {ran}   (baseline: exactly {base['ran']})")
print(f"  agree            {agree}   (baseline: at least {base['agree']})")
print(f"  sut_unsupported  {unsupported}   (baseline: at most {base['sut_unsupported']})")
print(f"  not_compared     {not_compared}   (baseline: at most {base_other})")
print(f"  disagree         {disagree}   (must be 0)")

failures = []
if disagree > 0:
    failures.append(f"disagree {disagree} > 0")
if ran != base["ran"]:
    failures.append(
        f"ran {ran} != baseline {base['ran']}: the corpus is not the pinned one "
        f"(remove desugar/corpus/bootstraptest and rerun to harvest it again)")
if agree < base["agree"]:
    failures.append(f"agree {agree} < baseline {base['agree']} (-{base['agree'] - agree})")
if unsupported > base["sut_unsupported"]:
    failures.append(
        f"sut_unsupported {unsupported} > baseline {base['sut_unsupported']} "
        f"(+{unsupported - base['sut_unsupported']})")
if not_compared > base_other:
    failures.append(f"not_compared {not_compared} > baseline {base_other}")

if failures:
    print()
    for f in failures:
        print(f"CONFORMANCE FAILED -- {f}")
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print(f"::error title=Conformance regressed::{'; '.join(failures)}")
    raise SystemExit(1)

rises = []
if agree > base["agree"]:
    rises.append(f"agree {base['agree']} -> {agree}")
if unsupported < base["sut_unsupported"]:
    rises.append(f"sut_unsupported {base['sut_unsupported']} -> {unsupported}")

if rises:
    detail = ", ".join(rises)
    print()
    print(f"CONFORMANCE IMPROVED -- {detail}")
    print(f"  Record it: scripts/check-conformance.sh --save {report}")
    # A rise is not a failure, but it must not be buried in one job's log: make
    # the owed re-measure visible in the pull request and the run summary.
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print(
            f"::warning title=Conformance baseline is behind the measured run::"
            f"{detail}. Record it with scripts/check-conformance.sh --save {report}")
    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_path:
        with open(summary_path, "a", encoding="utf-8") as fh:
            fh.write("### Conformance baseline is behind the measured run\n\n")
            fh.write(f"- {detail}\n")
            fh.write(f"- Record it: `scripts/check-conformance.sh --save {report}`\n")
else:
    print("\nCONFORMANCE OK -- no disagreement, and coverage holds the baseline.")
PY
