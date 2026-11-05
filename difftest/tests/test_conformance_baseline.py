"""The cheap half of the conformance baseline check.

`make conformance` calls `scripts/check-conformance.sh --check-corpus` before it
replays anything, so a harvest or gating change that moves the number of
programs fails in seconds. These tests pin that behaviour, and that a measured
improvement is surfaced without being treated as a failure.
"""

import json
import os
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "scripts" / "check-conformance.sh"


def write_baseline(path, *, ran, agree, unsupported=0, not_compared=0, disagree=0):
    path.write_text(
        json.dumps(
            {
                "corpus": "bootstraptest",
                "ran": ran,
                "agree": agree,
                "sut_unsupported": unsupported,
                "not_compared": not_compared,
                "disagree": disagree,
            }
        )
    )
    return path


def write_corpus(directory, count, *, manifest=None):
    directory.mkdir()
    for i in range(count):
        (directory / f"case_{i:03d}.rb").write_text("puts 1\n")
    if manifest is not None:
        (directory / "manifest.json").write_text(
            json.dumps([{"file": f"case_{i:03d}.rb"} for i in range(manifest)])
        )
    return directory


def run_corpus_check(tmp_path, *, baseline, corpus):
    env = os.environ.copy()
    env["CONFORMANCE_BASELINE"] = str(baseline)
    return subprocess.run(
        ["bash", str(SCRIPT), "--check-corpus", str(corpus)],
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )


def test_corpus_check_accepts_matching_baseline(tmp_path):
    baseline = write_baseline(tmp_path / "baseline.json", ran=2, agree=1, unsupported=1)
    corpus = write_corpus(tmp_path / "corpus", 2)

    result = run_corpus_check(tmp_path, baseline=baseline, corpus=corpus)

    assert result.returncode == 0, result.stdout + result.stderr
    assert "CORPUS OK" in result.stdout


def test_corpus_check_rejects_stale_ran(tmp_path):
    baseline = write_baseline(tmp_path / "baseline.json", ran=3, agree=3)
    corpus = write_corpus(tmp_path / "corpus", 2)

    result = run_corpus_check(tmp_path, baseline=baseline, corpus=corpus)

    assert result.returncode == 1
    assert "harvested corpus has 2 programs but the baseline records 3" in result.stdout
    assert "CORPUS CHECK FAILED" in result.stdout


def test_corpus_check_rejects_inconsistent_baseline_counts(tmp_path):
    baseline = write_baseline(tmp_path / "baseline.json", ran=2, agree=2, unsupported=1)
    corpus = write_corpus(tmp_path / "corpus", 2)

    result = run_corpus_check(tmp_path, baseline=baseline, corpus=corpus)

    assert result.returncode == 1
    assert "counts sum to 3, not its ran=2" in result.stdout


def test_corpus_check_rejects_manifest_mismatch(tmp_path):
    baseline = write_baseline(tmp_path / "baseline.json", ran=2, agree=2)
    corpus = write_corpus(tmp_path / "corpus", 2, manifest=1)

    result = run_corpus_check(tmp_path, baseline=baseline, corpus=corpus)

    assert result.returncode == 1
    assert "its manifest lists 1" in result.stdout


def test_corpus_check_reports_missing_corpus(tmp_path):
    baseline = write_baseline(tmp_path / "baseline.json", ran=2, agree=2)

    result = run_corpus_check(tmp_path, baseline=baseline, corpus=tmp_path / "missing")

    assert result.returncode == 2
    assert "no harvested corpus" in result.stdout


def test_improvement_is_surfaced_without_failing(tmp_path):
    baseline = write_baseline(tmp_path / "baseline.json", ran=2, agree=1, unsupported=1)
    report = tmp_path / "report"
    report.mkdir()
    (report / "summary.json").write_text(
        json.dumps({"total": 2, "verdicts": {"agree": 2, "sut_unsupported": 0, "disagree": 0}})
    )
    step_summary = tmp_path / "step-summary.md"
    env = os.environ.copy()
    env["CONFORMANCE_BASELINE"] = str(baseline)
    env["GITHUB_ACTIONS"] = "true"
    env["GITHUB_STEP_SUMMARY"] = str(step_summary)

    result = subprocess.run(
        ["bash", str(SCRIPT), str(report)],
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )

    assert result.returncode == 0, result.stdout + result.stderr
    assert "CONFORMANCE IMPROVED" in result.stdout
    assert "::warning title=Conformance baseline is behind the measured run" in result.stdout
    summary = step_summary.read_text()
    assert "Conformance baseline is behind the measured run" in summary
    assert "agree 1 -> 2" in summary
