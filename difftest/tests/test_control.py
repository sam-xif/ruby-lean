import pytest

from difftest.control import CRubyRunner


@pytest.fixture(scope="module")
def runner():
    return CRubyRunner(timeout=10.0)


def test_stdout_result_captured(runner):
    obs = runner.run('puts "hello"\n1 + 2\n')
    assert obs.stdout == "hello\n"
    assert obs.result_repr == "3"
    assert obs.exception is None


def test_exception_captured(runner):
    obs = runner.run('puts "before"\nraise ArgumentError, "bad"\nputs "after"\n')
    assert obs.stdout == "before\n"
    assert obs.result_repr is None
    assert obs.exception == ("ArgumentError", "bad")


def test_parse_check(runner):
    assert runner.check_parses("puts 1\n") is None
    assert runner.check_parses("def broken(\n") is not None


def test_timeout(runner):
    fast = CRubyRunner(timeout=2.0)
    obs = fast.run("loop { }\n")
    assert obs.timed_out


def test_nondeterminism_detected(runner):
    obs, why = runner.run_deterministic("puts rand(1000000)\n")
    assert obs is None
    assert "nondeterministic" in why


def test_program_with_braces_and_interp(runner):
    obs = runner.run('h = { a: 1 }\nputs "v=#{h[:a]}"\n')
    assert obs.stdout == "v=1\n"
