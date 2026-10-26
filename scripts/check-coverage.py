#!/usr/bin/env python3
"""Compare a unit-test suite's coverage with its recorded baseline.

    scripts/check-coverage.py SUITE           # what `make desugar-unit` etc. run
    scripts/check-coverage.py --save SUITE    # record this run as the new baseline

SUITE is one of the suites below. Each records, in its own
coverage-baseline.json, the line and branch coverage of the code it tests and
the files that were measured. Each may only move one way:

    line, branch   may not fall below the baseline
    files          every file the baseline lists that still exists must still
                   be measured: coverage cannot rise by measuring less

When a change raises a number, this prints the command that records it; commit
the new baseline in the same change.
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# suite -> (report, report format, baseline)
SUITES = {
    "desugar": (
        ".make/coverage/desugar/.resultset.json",
        "simplecov",
        "desugar/test/coverage-baseline.json",
    ),
    "emitter": (
        ".make/coverage/emitter/.resultset.json",
        "simplecov",
        "books/scripts/test/coverage-baseline.json",
    ),
    "difftest": (
        ".make/coverage/difftest.json",
        "coverage.py",
        "difftest/tests/coverage-baseline.json",
    ),
}


def percent(covered: int, total: int) -> float:
    """Rounded down to two places, so that a run never records more than it measured."""
    return 100.0 if total == 0 else math.floor(covered * 10000 / total) / 100


def read_simplecov(path: Path) -> dict:
    """SimpleCov's .resultset.json: per file, a count per line and per branch."""
    runs = list(json.loads(path.read_text()).values())
    if len(runs) != 1:
        raise SystemExit(f"{path} holds {len(runs)} runs; delete it and run the suite once")
    (result,) = runs
    lines = covered_lines = branches = covered_branches = 0
    files = []
    for name, cov in result["coverage"].items():
        files.append(str(Path(name).resolve().relative_to(ROOT)))
        counts = [c for c in cov["lines"] if c is not None]
        lines += len(counts)
        covered_lines += sum(1 for c in counts if c > 0)
        for arms in cov.get("branches", {}).values():
            branches += len(arms)
            covered_branches += sum(1 for c in arms.values() if c > 0)
    return {
        "line": percent(covered_lines, lines),
        "branch": percent(covered_branches, branches),
        "files": sorted(files),
    }


def read_coverage_py(path: Path) -> dict:
    """coverage.py's JSON report (`--cov-report=json`)."""
    report = json.loads(path.read_text())
    totals = report["totals"]
    files = [
        str((ROOT / "difftest" / name).resolve().relative_to(ROOT)) for name in report["files"]
    ]
    return {
        "line": percent(totals["covered_lines"], totals["num_statements"]),
        "branch": percent(totals["covered_branches"], totals["num_branches"]),
        "files": sorted(files),
    }


def main(argv: list[str]) -> int:
    save = "--save" in argv
    args = [a for a in argv if a != "--save"]
    if len(args) != 1 or args[0] not in SUITES:
        print(f"usage: {sys.argv[0]} [--save] {{{','.join(SUITES)}}}", file=sys.stderr)
        return 2
    suite = args[0]
    report, fmt, baseline = SUITES[suite]
    report_path, baseline_path = ROOT / report, ROOT / baseline
    if not report_path.exists():
        print(f"no coverage report at {report_path}: run the suite first", file=sys.stderr)
        return 2
    run = read_simplecov(report_path) if fmt == "simplecov" else read_coverage_py(report_path)

    if save:
        baseline_path.write_text(json.dumps(run, indent=2) + "\n")
        print(f"baseline saved: {baseline_path.relative_to(ROOT)}")
        return 0

    base = json.loads(baseline_path.read_text())
    print(f"{suite} unit-test coverage")
    print(f"  line    {run['line']:6.2f}%   (baseline: at least {base['line']:.2f}%)")
    print(f"  branch  {run['branch']:6.2f}%   (baseline: at least {base['branch']:.2f}%)")
    print(f"  files   {len(run['files']):6d}    (baseline: {len(base['files'])})")

    failures = []
    for key in ("line", "branch"):
        if run[key] < base[key]:
            failures.append(f"{key} coverage {run[key]:.2f}% < baseline {base[key]:.2f}%")
    unmeasured = [f for f in base["files"] if (ROOT / f).exists() and f not in run["files"]]
    if unmeasured:
        failures.append("no longer measured: " + ", ".join(unmeasured))
    if failures:
        print()
        for f in failures:
            print(f"COVERAGE FAILED -- {f}")
        return 1

    if (
        run["line"] > base["line"]
        or run["branch"] > base["branch"]
        or run["files"] != base["files"]
    ):
        print(f"\nCOVERAGE IMPROVED -- record it: scripts/check-coverage.py --save {suite}")
    else:
        print("\nCOVERAGE OK -- the baseline holds.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
