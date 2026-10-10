"""The `rubycore` CLI contract: an unrecognized flag is a harness error.

`--check` was removed with the pre-ratchet type checker, but a stale caller that
still passes it must fail loudly rather than get a program run in place of the
verdict it asked for (issue #35). The flag vocabulary is checked before stdin is
read, so these tests need no program input.
"""

import subprocess

import pytest

from difftest.sorbet import FragmentChecker

# The binary the rest of the suite drives; skip when the model is not built.
requires_rubycore = pytest.mark.skipif(
    not FragmentChecker().lean_bin.exists(),
    reason="Lean rubycore binary not built",
)

RUBYCORE = FragmentChecker().lean_bin


def _run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(RUBYCORE), *args], input="", capture_output=True, text=True, timeout=30
    )


@requires_rubycore
@pytest.mark.parametrize("flag", ["--check", "--bogus", "--check-tl", "--assn"])
def test_removed_and_unknown_flags_are_harness_errors(flag):
    """A removed or misspelled flag exits 1 with a message naming it — never a
    silent program run (exit 0)."""
    proc = _run(flag)
    assert proc.returncode == 1, (proc.returncode, proc.stdout, proc.stderr)
    assert flag in proc.stderr
    assert proc.stdout == ""


@requires_rubycore
def test_a_value_flag_without_its_value_is_a_harness_error():
    proc = _run("--fuel")
    assert proc.returncode == 1
    assert "--fuel" in proc.stderr


@requires_rubycore
@pytest.mark.parametrize(
    "args",
    [
        ["--steps"],
        ["--fragment"],
        ["--sigs"],
        ["--lean-term"],
        ["--preload-json"],
    ],
)
def test_known_flags_are_not_rejected_by_the_vocabulary_check(args):
    """The guard must not reject the flags the pipeline actually passes. With
    empty stdin a decode error is expected *after* the check, so a rejection
    would show as the vocabulary message; assert only that it is not that."""
    proc = _run(*args)
    assert "unrecognized argument" not in proc.stderr, proc.stderr
