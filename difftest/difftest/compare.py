"""Verdicts: the outcome of one test case through the engine."""

from __future__ import annotations

import enum
from dataclasses import dataclass, field

from .observation import Observation
from .testcase import TestCase


class Verdict(enum.Enum):
    AGREE = "agree"
    DISAGREE = "disagree"
    SUT_UNSUPPORTED = "sut_unsupported"  # SUT gated the program out of its fragment
    CONTROL_INVALID = "control_invalid"  # parse error / timeout / nondeterministic under control
    HARNESS_ERROR = "harness_error"  # the engine itself failed to observe


@dataclass
class CaseResult:
    case: TestCase
    verdict: Verdict
    reason: str | None = None  # required for every non-AGREE verdict ("no silent caps")
    control_obs: Observation | None = None
    sut_obs: Observation | None = None
    minimized: bool = False  # True for a shrunk reproducer (tier 1)
    timings: dict = field(default_factory=dict)

    def to_json(self) -> dict:
        return {
            "id": self.case.id,
            "tier": self.case.tier,
            "source": self.case.source,
            "provenance": self.case.provenance,
            "verdict": self.verdict.value,
            "reason": self.reason,
            "control_obs": self.control_obs.to_json() if self.control_obs else None,
            "sut_obs": self.sut_obs.to_json() if self.sut_obs else None,
            "minimized": self.minimized,
            "timings": self.timings,
        }


def compare(control: Observation, sut: Observation) -> tuple[Verdict, str | None]:
    a, b = control.normalized(), sut.normalized()
    if a == b:
        return Verdict.AGREE, None
    # A SUT wall-clock timeout (control completed in time) is inconclusive, not a
    # wrong answer — the model was too slow, it did not disagree. Classify it as
    # out-of-fragment (same neutral bucket as an explicit Unsupported gate). True
    # nontermination is separately caught by the model's step-fuel limit (which
    # exits cleanly as Unsupported), so this only absorbs "correct but too slow".
    if b.timed_out and not a.timed_out:
        return Verdict.SUT_UNSUPPORTED, "sut timeout (too slow; control completed within the limit)"
    parts = []
    if a.stdout != b.stdout:
        parts.append(f"stdout: {a.stdout!r} vs {b.stdout!r}")
    if a.result_repr != b.result_repr:
        parts.append(f"result: {a.result_repr!r} vs {b.result_repr!r}")
    if a.exception != b.exception:
        parts.append(f"exception: {a.exception!r} vs {b.exception!r}")
    if a.timed_out != b.timed_out:
        parts.append(f"timed_out: {a.timed_out} vs {b.timed_out}")
    return Verdict.DISAGREE, " | ".join(parts)
