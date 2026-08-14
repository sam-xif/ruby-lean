"""The regressions corpus: loading, status reconciliation, and auto-filing (N41).

These tests exist because the mechanism is only worth having if it can go **red**.
A pinned-failure corpus that cannot fail is indistinguishable from an empty one,
and that is exactly the state `corpus/regressions/` was in before this tier: 16
files on disk, read by nothing.
"""

import json

import pytest

from difftest.campaign import _file_regression
from difftest.compare import CaseResult, Verdict
from difftest.observation import Observation
from difftest.sources import (REGRESSION_FAILURES, load_regressions_corpus,
                              regression_outcome)
from difftest.testcase import TestCase


def _write_case(tmp_path, name, source='puts "x"\n', meta=None):
    (tmp_path / f"{name}.rb").write_text(source)
    if meta is not None:
        (tmp_path / f"{name}.json").write_text(json.dumps(meta))


# ─── loading ────────────────────────────────────────────────────────────────


def test_missing_directory_is_not_an_error(tmp_path):
    """A project with no known defects is the goal, not a harness failure."""
    assert load_regressions_corpus(tmp_path / "nope") == []


def test_case_without_sidecar_defaults_to_open(tmp_path):
    """The campaign writes the .rb the moment a disagreement is confirmed, so
    `open` cannot be wrong at write time."""
    _write_case(tmp_path, "bare")
    (case,) = load_regressions_corpus(tmp_path)
    assert case.provenance["status"] == "open"


def test_sidecar_status_is_read(tmp_path):
    _write_case(tmp_path, "guard", meta={"status": "fixed"})
    (case,) = load_regressions_corpus(tmp_path)
    assert case.provenance["status"] == "fixed"


def test_unknown_status_is_rejected_loudly(tmp_path):
    """A typo must not silently become 'not checked'."""
    _write_case(tmp_path, "typo", meta={"status": "wontfix"})
    with pytest.raises(ValueError, match="wontfix"):
        load_regressions_corpus(tmp_path)


# ─── reconciliation: the whole point ────────────────────────────────────────


@pytest.mark.parametrize(
    "status,verdict,expected",
    [
        ("fixed", "agree", "held"),
        ("fixed", "agree_weakened", "held"),
        ("open", "disagree", "still_open"),
        # the two that must fail, in both directions
        ("fixed", "disagree", "regressed"),
        ("open", "agree", "unexpectedly_fixed"),
        # neither pass nor fail: the case stopped testing what it pinned
        ("open", "sut_unsupported", "gated"),
        ("fixed", "sut_unsupported", "gated"),
        ("fixed", "control_invalid", "unusable"),
        ("open", "harness_error", "unusable"),
    ],
)
def test_outcome_reconciliation(status, verdict, expected):
    assert regression_outcome(status, verdict) == expected


def test_a_known_open_defect_does_not_redden_the_run():
    """`still_open` is the expected state of a filed defect. If it counted as a
    failure the corpus could not hold one, which would defeat the tier."""
    assert regression_outcome("open", "disagree") not in REGRESSION_FAILURES


def test_both_failure_directions_are_failures():
    assert regression_outcome("fixed", "disagree") in REGRESSION_FAILURES
    assert regression_outcome("open", "agree") in REGRESSION_FAILURES


# ─── auto-filing ────────────────────────────────────────────────────────────


def _minimal(source='puts "boom"\n'):
    return CaseResult(
        case=TestCase(id="tier1-00042", source=source, tier=1),
        verdict=Verdict.DISAGREE,
        reason="stdout: 'a' vs 'b'",
        control_obs=Observation(stdout="a", result_repr=None, exception=None, timed_out=False),
        sut_obs=Observation(stdout="b", result_repr=None, exception=None, timed_out=False),
    )


def test_filing_writes_program_and_a_self_describing_sidecar(tmp_path):
    path = _file_regression(tmp_path, _minimal(), "tier1", seed=7)
    assert path.read_text() == 'puts "boom"\n'
    meta = json.loads(path.with_suffix(".json").read_text())
    assert meta["status"] == "open"
    assert meta["seed"] == 7
    assert meta["diff"] == "stdout: 'a' vs 'b'"
    # the observations are recorded, so a reader need not re-derive the defect
    assert meta["control"]["stdout"] == "a"
    assert meta["sut"]["stdout"] == "b"


def test_filing_round_trips_through_the_loader(tmp_path):
    _file_regression(tmp_path, _minimal(), "tier1", seed=None)
    (case,) = load_regressions_corpus(tmp_path)
    assert case.provenance["status"] == "open"
    assert case.source == 'puts "boom"\n'


def test_refiling_never_clobbers_a_human_status(tmp_path):
    """Someone marks a case fixed; a later campaign re-files the same id. The
    status is a human judgement and the machine must not reset it — otherwise a
    guard silently reverts to `open` and stops guarding."""
    _file_regression(tmp_path, _minimal(), "tier1", seed=None)
    meta_path = tmp_path / "tier1-00042-minimized.json"
    meta = json.loads(meta_path.read_text())
    meta["status"] = "fixed"
    meta_path.write_text(json.dumps(meta))

    _file_regression(tmp_path, _minimal(), "tier1", seed=None)
    assert json.loads(meta_path.read_text())["status"] == "fixed"
