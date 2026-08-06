"""Campaign orchestration: case -> control -> SUT -> verdict."""

from __future__ import annotations

import time
from collections.abc import Iterable

from .compare import CaseResult, Verdict, compare
from .control import CRubyRunner, HarnessError
from .sut import SystemUnderTest, Unsupported
from .testcase import TestCase


def run_case(case: TestCase, control: CRubyRunner, sut: SystemUnderTest) -> CaseResult:
    t0 = time.monotonic()
    syntax_err = control.check_parses(case.source)
    if syntax_err is not None:
        return CaseResult(case, Verdict.CONTROL_INVALID, reason=f"parse error: {syntax_err}")

    try:
        control_obs, why = control.run_deterministic(case.source)
    except HarnessError as e:
        return CaseResult(case, Verdict.HARNESS_ERROR, reason=str(e))
    if control_obs is None:
        return CaseResult(case, Verdict.CONTROL_INVALID, reason=why)
    t1 = time.monotonic()

    try:
        sut_out = sut.run(case.source)
    except HarnessError as e:
        return CaseResult(case, Verdict.HARNESS_ERROR, reason=str(e), control_obs=control_obs)
    t2 = time.monotonic()

    timings = {"control_s": round(t1 - t0, 3), "sut_s": round(t2 - t1, 3)}
    if isinstance(sut_out, Unsupported):
        return CaseResult(
            case,
            Verdict.SUT_UNSUPPORTED,
            reason=sut_out.reason,
            control_obs=control_obs,
            timings=timings,
        )
    # A SUT may carry its own comparator, taking the case as well as the two
    # observations. The default relation is "the two implementations should
    # produce the same observation", but a *metamorphic* SUT (sig-strip: same
    # implementation, transformed program) relates the two runs differently and
    # may need the source to do so — see `compare.gradual_guarantee_compare`.
    relation = getattr(sut, "compare", None)
    verdict, reason = (
        relation(control_obs, sut_out, case) if relation else compare(control_obs, sut_out)
    )
    return CaseResult(
        case, verdict, reason=reason, control_obs=control_obs, sut_obs=sut_out, timings=timings
    )


def run_campaign(
    cases: Iterable[TestCase],
    control: CRubyRunner,
    sut: SystemUnderTest,
    on_result=None,
) -> list[CaseResult]:
    results = []
    for case in cases:
        result = run_case(case, control, sut)
        results.append(result)
        if on_result:
            on_result(result)
    return results
