"""`run_campaign` over a corpus: cases run at once with `jobs`, results stay in order."""

import threading
import time

import pytest
from difftest.compare import Verdict
from difftest.observation import Observation
from difftest.runner import run_campaign
from difftest.testcase import TestCase as Case  # aliased: pytest tries to collect *TestCase


def _obs(stdout: str) -> Observation:
    return Observation(stdout=stdout, result_repr="nil", exception=None)


class _Control:
    """A control that prints each program's source, after `before_run(source)`."""

    def __init__(self, before_run=None):
        self.before_run = before_run or (lambda source: None)

    def check_parses(self, source):
        return None

    def run_deterministic(self, source):
        self.before_run(source)
        return _obs(source), None


class _EchoSUT:
    name = "echo"

    def run(self, source):
        return _obs(source)


def _cases(n: int) -> list[Case]:
    return [Case(id=f"c{i}", source=f"p{i}", tier=0) for i in range(n)]


def test_one_job_runs_every_case_in_order():
    seen = []
    results = run_campaign(_cases(4), _Control(), _EchoSUT(), on_result=seen.append)
    assert [r.case.id for r in results] == ["c0", "c1", "c2", "c3"]
    assert seen == results
    assert all(r.verdict == Verdict.AGREE for r in results)


def test_cases_run_at_once_with_jobs():
    # Every case waits until all three have started: this finishes only if they
    # run at the same time, and fails with BrokenBarrierError otherwise.
    barrier = threading.Barrier(3, timeout=10)
    results = run_campaign(
        _cases(3), _Control(before_run=lambda source: barrier.wait()), _EchoSUT(), jobs=3
    )
    assert [r.verdict for r in results] == [Verdict.AGREE] * 3


def test_results_keep_the_order_of_the_cases_whatever_order_they_finish_in():
    # The first case finishes last.
    delays = {"p0": 0.2, "p1": 0.0, "p2": 0.1, "p3": 0.0}
    seen = []
    results = run_campaign(
        _cases(4),
        _Control(before_run=lambda source: time.sleep(delays[source])),
        _EchoSUT(),
        on_result=seen.append,
        jobs=4,
    )
    assert [r.case.id for r in results] == ["c0", "c1", "c2", "c3"]
    assert [r.case.id for r in seen] == ["c0", "c1", "c2", "c3"]


def test_on_result_is_called_on_the_calling_thread():
    threads = set()
    run_campaign(
        _cases(4),
        _Control(),
        _EchoSUT(),
        on_result=lambda r: threads.add(threading.get_ident()),
        jobs=4,
    )
    assert threads == {threading.get_ident()}


def test_a_failing_case_is_raised_not_lost():
    def boom(source):
        if source == "p2":
            raise RuntimeError("control crashed")

    with pytest.raises(RuntimeError, match="control crashed"):
        run_campaign(_cases(4), _Control(before_run=boom), _EchoSUT(), jobs=2)


def test_jobs_must_be_positive():
    with pytest.raises(ValueError, match="at least 1"):
        run_campaign(_cases(1), _Control(), _EchoSUT(), jobs=0)
