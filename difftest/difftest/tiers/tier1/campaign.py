"""Tier-1 campaign: drive the strategies through Hypothesis.

The campaign is a Hypothesis property asserting control/SUT agreement. This
buys us Hypothesis's shrinker for free: the first disagreement is minimized
automatically, and the minimal reproducer is persisted to corpus/regressions/.

Note: after a disagreement is found, Hypothesis stops generating and shrinks,
so the run ends early — the report flags this. Records produced during the
shrink phase are recorded too (they are real oracle runs), tagged in
provenance with phase="shrink-search".
"""

from __future__ import annotations

import itertools
from pathlib import Path

from hypothesis import HealthCheck, Phase, given
from hypothesis import seed as hyp_seed
from hypothesis import settings as hyp_settings

from ...compare import CaseResult, Verdict
from ...control import CRubyRunner
from ...report import Reporter
from ...runner import run_case
from ...sut import SystemUnderTest
from ...testcase import TestCase
from .render import render_program
from .strategies import programs


class _Disagreement(Exception):
    def __init__(self, result: CaseResult):
        self.result = result
        super().__init__(result.reason)


def run_tier1_campaign(
    control: CRubyRunner,
    sut: SystemUnderTest,
    reporter: Reporter,
    n: int,
    seed: int | None = None,
    regressions_dir: Path | None = None,
) -> dict:
    counter = itertools.count()
    found_disagreement = False

    def prop(prog):
        nonlocal found_disagreement
        src = render_program(prog)
        case = TestCase(
            id=f"tier1-{next(counter):05d}",
            source=src,
            tier=1,
            provenance={"generator": "hypothesis", "seed": seed,
                        "phase": "shrink-search" if found_disagreement else "generate"},
        )
        result = run_case(case, control, sut)
        reporter.record(result)
        if result.verdict == Verdict.DISAGREE:
            found_disagreement = True
            raise _Disagreement(result)

    wrapped = given(programs())(prop)
    wrapped = hyp_settings(
        max_examples=n,
        deadline=None,
        database=None,
        derandomize=False,
        suppress_health_check=list(HealthCheck),
        phases=[Phase.generate, Phase.shrink],
        print_blob=False,
    )(wrapped)
    if seed is not None:
        wrapped = hyp_seed(seed)(wrapped)

    minimal: CaseResult | None = None
    try:
        wrapped()
    except _Disagreement as e:
        minimal = e.result
    except BaseExceptionGroup as eg:  # hypothesis may group multiple failures
        for sub in eg.exceptions:
            if isinstance(sub, _Disagreement):
                minimal = sub.result
                break
        if minimal is None:
            raise

    extra: dict = {"tier1": {"requested_examples": n, "seed": seed,
                             "stopped_early_on_disagreement": minimal is not None}}
    if minimal is not None:
        minimal.minimized = True
        reporter.record(minimal)
        if regressions_dir is not None:
            regressions_dir.mkdir(parents=True, exist_ok=True)
            path = regressions_dir / f"{minimal.case.id}-minimized.rb"
            path.write_text(minimal.case.source)
            extra["tier1"]["minimized_reproducer"] = str(path)
    return extra
