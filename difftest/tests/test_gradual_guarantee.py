"""The gradual-guarantee probe: the relation, and that it actually detects."""

import pytest

from difftest.compare import Verdict, gradual_guarantee_compare
from difftest.observation import Observation
from difftest.runner import run_case
from difftest.control import CRubyRunner
from difftest.sorbet import sorbet_runtime_available
from difftest.sut import SigStripSUT
from difftest.testcase import TestCase as Case  # aliased: pytest tries to collect *TestCase

requires_runtime = pytest.mark.skipif(
    not sorbet_runtime_available(), reason="sorbet-runtime gem not installed"
)


def obs(stdout="", result=None, exc=None):
    return Observation(stdout=stdout, result_repr=result, exception=exc)


SIG_ERR = ("TypeError", "Parameter 'x': Expected type Integer, got type String")


# --------------------------------------------------------------------------
# the relation itself
# --------------------------------------------------------------------------


def test_identical_observations_agree():
    v, why = gradual_guarantee_compare(obs("1\n"), obs("1\n"), obs("1\n"))
    assert v is Verdict.AGREE and why is None


def test_trapped_escaping_error_is_licensed():
    # precise blames; stripped runs on; with enforcement off the precise
    # program matches the stripped one -> attributable to enforcement
    v, why = gradual_guarantee_compare(
        obs("1\n", exc=SIG_ERR), obs("1\n2\n"), obs("1\n2\n")
    )
    assert v is Verdict.AGREE_WEAKENED
    assert "attributable to runtime enforcement" in why


def test_trapped_but_rescued_error_is_licensed():
    # The case with no exception anywhere: the program rescued its own sig
    # violation, so the two variants differ only in stdout. Keying off the
    # exception would call this a violation; attribution gets it right.
    v, why = gradual_guarantee_compare(
        obs("1\ntrapped\n3\n"), obs("1\ntwo\n3\n"), obs("1\ntwo\n3\n")
    )
    assert v is Verdict.AGREE_WEAKENED
    assert "rescued by the program" in why


def test_difference_not_attributable_to_enforcement_is_a_violation():
    # unchecked != stripped: the annotations changed behavior by something
    # other than trapping, which the guarantee forbids.
    v, why = gradual_guarantee_compare(obs("a\n"), obs("b\n"), obs("a\n"))
    assert v is Verdict.DISAGREE
    assert "GUARANTEE VIOLATION" in why


def test_stripped_variant_blaming_is_a_violation():
    # Stripping removes checks, so the less precise variant must never blame.
    v, why = gradual_guarantee_compare(obs("1\n"), obs("", exc=SIG_ERR), obs("1\n"))
    assert v is Verdict.DISAGREE
    assert "blames where the annotated one did not" in why


def test_sut_timeout_is_inconclusive_not_a_violation():
    slow = Observation(stdout="", result_repr=None, exception=None, timed_out=True)
    v, _ = gradual_guarantee_compare(obs("1\n"), slow, obs("1\n"))
    assert v is Verdict.SUT_UNSUPPORTED


# --------------------------------------------------------------------------
# end to end: the probe must be *sensitive*, not merely quiet
# --------------------------------------------------------------------------

# A real gradual-guarantee violation in sorbet-runtime, found by this probe:
# the checking wrapper is observable through reflection. It renames the
# parameter (`:x` -> `:arg0`) and appends a block parameter, so a program that
# reflects on its own signature behaves differently purely because annotations
# are present — not because anything was trapped. This is the probe's
# detection self-test (the role `--inject-bug` plays for the desugar SUT):
# a probe that never fires proves nothing.
REFLECTION_VIOLATION = """\
# typed: true
require "sorbet-runtime"

class C
  extend T::Sig

  sig { params(x: Integer).returns(String) }
  def f(x)
    x.to_s
  end
end

puts C.new.f(1)
puts C.instance_method(:f).parameters.inspect
"""

CLEAN_PROGRAM = """\
# typed: true
require "sorbet-runtime"
extend T::Sig

sig { params(x: Integer).returns(String) }
def f(x)
  x.to_s
end

puts f(1)
"""


@requires_runtime
@pytest.mark.parametrize(
    "source,expected",
    [
        (CLEAN_PROGRAM, Verdict.AGREE),
        (REFLECTION_VIOLATION, Verdict.DISAGREE),
    ],
    ids=["holds", "detects"],
)
def test_probe_end_to_end(source, expected):
    result = run_case(
        Case(id="t", source=source, tier=4),
        CRubyRunner(timeout=30.0),
        SigStripSUT(),
    )
    assert result.verdict is expected, result.reason
