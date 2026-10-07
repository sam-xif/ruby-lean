"""Shared test configuration.

A few tests need Sorbet or the model's executable and skip when one is missing,
so that the suite can run on a machine without them. `make difftest-test` has
both, and sets DIFFTEST_NO_SKIPS=1: a skipped test is then reported as a
failure, so a missing tool cannot quietly turn a test off.
"""
import os

import pytest


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_makereport(item, call):
    outcome = yield
    report = outcome.get_result()
    if os.environ.get("DIFFTEST_NO_SKIPS") == "1" and report.skipped and not hasattr(report, "wasxfail"):
        report.outcome = "failed"
        report.longrepr = f"skipped, and DIFFTEST_NO_SKIPS=1 does not allow it: {report.longrepr}"
