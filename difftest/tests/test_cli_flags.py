"""The `rubycore` CLI rejects a numeric flag with a malformed value.

`--fuel`, `--trace-from` and `--trace` all take numbers. Before this guard a
mistyped value fell back to the default, so a caller that asked for one limit
got a plausible-looking run with another. These tests drive the built binary;
stdin is empty, so the program is only reached when the arguments are accepted.

`make difftest-test` builds the model first (`lean-exes`), so the binary this
reads is present wherever the suite runs under `make`.
"""

import subprocess

import pytest
from difftest.sorbet import FragmentChecker

RUBYCORE = FragmentChecker().lean_bin


def _run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(RUBYCORE), *args],
        check=False,
        input="",
        capture_output=True,
        text=True,
        timeout=30,
    )


@pytest.mark.parametrize(
    "args",
    [
        ["--fuel", "abc"],
        ["--fuel", "10x"],
        ["--trace-from", "abc"],
        ["--trace", "abc"],
    ],
)
def test_a_malformed_numeric_value_is_a_harness_error(args):
    """A non-numeric value exits 1, names the flag and prints no observation."""
    proc = _run(*args)
    assert proc.returncode == 1, (proc.returncode, proc.stdout, proc.stderr)
    assert args[0] in proc.stderr
    assert "expects a number" in proc.stderr or "expects a step count" in proc.stderr
    assert proc.stdout == ""


@pytest.mark.parametrize("flag", ["--fuel", "--trace-from"])
def test_a_missing_numeric_value_is_a_harness_error(flag):
    proc = _run(flag)
    assert proc.returncode == 1
    assert flag in proc.stderr
    assert proc.stdout == ""


@pytest.mark.parametrize(
    "args",
    [
        ["--fuel", "10"],
        ["--trace", "10"],
        ["--trace"],
        ["--trace-at", "abc"],
        ["--trace-at", "123abc"],
        ["--trace", "10", "--trace-at", "needle"],
    ],
)
def test_valid_numbers_and_arbitrary_trace_needles_are_accepted(args):
    """The guard must not reject what the CLI documents as a value. Empty stdin
    then fails to decode, which is a different, later error."""
    proc = _run(*args)
    assert "expects a number" not in proc.stderr, proc.stderr
    assert "expects a step count" not in proc.stderr, proc.stderr
    assert "bad input JSON" in proc.stderr, proc.stderr
