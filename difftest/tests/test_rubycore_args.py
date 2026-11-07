"""The `rubycore` CLI contract for its own arguments.

`rubycore` reads a program on stdin, so every argument it accepts is a flag. A
removed flag such as `--check` (from the pre-ratchet type checker) or a mistyped
limit must fail loudly instead of being ignored: a stale caller must not get a
program run in place of the answer it asked for, and a caller that asks for
`--fuel 10` must not silently get the default. `make difftest-test` builds the
binary (`lean-exes`) before running this suite.
"""

import json
import subprocess

import pytest
from difftest.sorbet import FragmentChecker

RUBYCORE = FragmentChecker().lean_bin
PROGRAM = json.dumps({"v": 5, "ast": ["int", 1]})


def _run(*args: str, stdin: str = "") -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(RUBYCORE), *args],
        check=False,
        input=stdin,
        capture_output=True,
        text=True,
        timeout=30,
    )


@pytest.mark.parametrize("flag", ["--check", "--check-tl", "--assn", "--bogus"])
def test_removed_and_unknown_flags_are_harness_errors(flag):
    """A removed or misspelled flag exits 1 and names itself, never a silent run."""
    proc = _run(flag, stdin=PROGRAM)
    assert proc.returncode == 1, (proc.returncode, proc.stdout, proc.stderr)
    assert flag in proc.stderr
    assert proc.stdout == ""


def test_a_stray_positional_argument_is_a_harness_error():
    proc = _run("program.json", stdin=PROGRAM)
    assert proc.returncode == 1, (proc.returncode, proc.stdout, proc.stderr)
    assert "program.json" in proc.stderr
    assert proc.stdout == ""


@pytest.mark.parametrize(
    "args",
    [
        ["--fuel"],
        ["--trace-from"],
        ["--trace-at"],
        ["--fuel", "abc"],
        ["--fuel", "10x"],
        ["--trace-from", "abc"],
        ["--trace", "abc"],
    ],
)
def test_missing_or_malformed_values_are_harness_errors(args):
    """A value flag with no value, or a number that does not parse, exits 1."""
    proc = _run(*args, stdin=PROGRAM)
    assert proc.returncode == 1, (proc.returncode, proc.stdout, proc.stderr)
    assert args[0] in proc.stderr
    assert "expects" in proc.stderr
    assert proc.stdout == ""


@pytest.mark.parametrize(
    "args",
    [
        [],
        ["--fuel", "10"],
        ["--steps"],
        ["--fragment"],
        ["--sigs"],
        ["--lean-term"],
        ["--preload-json"],
        ["--trace"],
        ["--trace", "10"],
        ["--trace", "--steps"],
        ["--trace-from", "3", "--trace-at", "needle"],
        ["--trace-at", "-x"],
    ],
)
def test_documented_arguments_are_accepted(args):
    """The guard must not reject the flags and values the CLI documents.

    The minimal program on stdin then runs; `--trace-at "-x"` shows that a
    trace needle is an arbitrary string, not a flag.
    """
    proc = _run(*args, stdin=PROGRAM)
    assert "refusing to run the program" not in proc.stderr, proc.stderr
    assert proc.returncode == 0, (proc.returncode, proc.stdout, proc.stderr)


def test_a_program_still_runs_with_a_valid_limit():
    """The validation sits before the run, not in place of it."""
    proc = _run("--fuel", "10", stdin=PROGRAM)
    assert proc.returncode == 0, (proc.returncode, proc.stdout, proc.stderr)
    assert json.loads(proc.stdout)["result_repr"] == "1"
