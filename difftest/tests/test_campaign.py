"""Mixed-tier campaign: mix parsing, arm thresholds, and end-to-end runs."""

import json

import pytest

from difftest.campaign import WEIGHT_RESOLUTION, _thresholds, parse_mix, run_generative_campaign
from difftest.control import CRubyRunner
from difftest.observation import Observation
from difftest.report import Reporter
from difftest.sources import load_corpus_cases
from difftest.sut import IdentityCRubySUT


def test_parse_mix():
    assert parse_mix("tier1=0.99,tier3=0.01") == {"tier1": 0.99, "tier3": 0.01}
    assert parse_mix("tier1=1") == {"tier1": 1.0}


@pytest.mark.parametrize("bad", ["tier1", "tier1=0", "tier1=-1", "tier1=0.5,tier1=0.5", "=3"])
def test_parse_mix_rejects(bad):
    with pytest.raises(ValueError):
        parse_mix(bad)


def test_thresholds_cover_resolution_and_keep_every_arm():
    t = _thresholds({"tier1": 0.999, "tier3": 0.001})
    assert t[-1][1] == WEIGHT_RESOLUTION
    slots = [t[0][1]] + [b - a for (_, a), (_, b) in zip(t, t[1:])]
    assert all(s >= 1 for s in slots)  # no requested arm is silently dead


def _write_corpus(tmp_path, sources):
    for i, src in enumerate(sources):
        (tmp_path / f"{i:03d}.rb").write_text(src)
        (tmp_path / f"{i:03d}.json").write_text(json.dumps({"tier": 3, "category": "t"}))
    return load_corpus_cases(tmp_path, default_tier=3)


def test_mixed_campaign_agrees_and_counts_arms(tmp_path):
    control = CRubyRunner()
    corpus = _write_corpus(tmp_path, ['puts "c0"\n', "p 1 + 1\n", "p [1, 2][5]\n"])
    reporter = Reporter(tmp_path / "report")
    extra = run_generative_campaign(
        control, IdentityCRubySUT(control), reporter, n=12, seed=1234,
        mix={"tier1": 0.5, "tier3": 0.5}, corpus_cases={"tier3": corpus},
    )
    reporter.finalize("identity")
    counts = extra["campaign"]["arm_counts"]
    assert sum(counts.values()) == 12
    assert set(counts) == {"tier1", "tier3"}
    assert all(r.verdict.value == "agree" for r in reporter.results)
    assert all(r.case.provenance["arm"] in ("tier1", "tier3") for r in reporter.results)


def test_mixed_campaign_requires_corpus_for_corpus_arms(tmp_path):
    control = CRubyRunner()
    with pytest.raises(ValueError, match="no corpus cases"):
        run_generative_campaign(
            control, IdentityCRubySUT(control), Reporter(tmp_path / "r"), n=1,
            mix={"tier3": 1.0}, corpus_cases={},
        )


class _WrongOnMarker:
    """Identity SUT except it lies about any program containing MARKER."""

    MARKER = "6660"
    name = "wrong-on-marker"

    def __init__(self, control):
        self.control = control

    def run(self, source):
        if self.MARKER in source:
            return Observation(stdout="WRONG", result_repr="nil", exception=None)
        return self.control.run(source)


def test_mixed_campaign_reports_disagreeing_corpus_case(tmp_path):
    control = CRubyRunner()
    corpus = _write_corpus(tmp_path, ["p 6660\n", 'puts "fine"\n'])
    reporter = Reporter(tmp_path / "report")
    extra = run_generative_campaign(
        control, _WrongOnMarker(control), reporter, n=30, seed=7,
        mix={"tier3": 1.0}, corpus_cases={"tier3": corpus},
    )
    summary = reporter.finalize("wrong-on-marker")
    assert extra["campaign"]["stopped_early_on_disagreement"]
    assert extra["campaign"]["disagreeing_corpus_case"] == "000.rb"
    assert "minimized_reproducer" not in extra["campaign"]
    assert summary["verdicts"]["disagree"] >= 1
