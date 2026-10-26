"""Shared test configuration.

A few tests need Sorbet or the model's executable and skip when one is missing,
so that the suite can run on a machine without them. `make difftest-test` has
both, and sets DIFFTEST_NO_SKIPS=1: a skipped test is then reported as a
failure, so a missing tool cannot quietly turn a test off.

Property tests are derandomized: Hypothesis derives its examples from each
test's source, so a run passes or fails the same way every time and a failure
is not luck. HYPOTHESIS_PROFILE=random explores with fresh examples instead.
"""

import os

import pytest
from hypothesis import settings

settings.register_profile("deterministic", derandomize=True, database=None)
settings.register_profile("random", database=None)
settings.load_profile(os.environ.get("HYPOTHESIS_PROFILE", "deterministic"))


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_makereport(item, call):
    outcome = yield
    report = outcome.get_result()
    if (
        os.environ.get("DIFFTEST_NO_SKIPS") == "1"
        and report.skipped
        and not hasattr(report, "wasxfail")
    ):
        report.outcome = "failed"
        report.longrepr = f"skipped, and DIFFTEST_NO_SKIPS=1 does not allow it: {report.longrepr}"
