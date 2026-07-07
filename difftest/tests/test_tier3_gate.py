"""The tier-3 validation gate, tested offline (no API involved)."""

from difftest.control import CRubyRunner
from difftest.tiers.tier3.generate import _validate
from difftest.tiers.tier3.prompts import CATEGORIES, build_prompt

runner = CRubyRunner(timeout=5.0)


def test_accepts_good_program():
    assert _validate('puts [1, 2].map { |x| x * 2 }.inspect\n', runner) is None


def test_accepts_deterministic_raiser():
    assert _validate('raise ArgumentError, "always"\n', runner) is None


def test_rejects_parse_error():
    assert "parse error" in _validate("def broken(\n", runner)


def test_rejects_nondeterminism():
    assert "nondeterministic" in _validate("puts rand(10**9)\n", runner)


def test_rejects_timeout():
    fast = CRubyRunner(timeout=2.0)
    assert _validate("loop { }\n", fast) == "timeout"


def test_prompts_build_for_every_category():
    for cat in CATEGORIES:
        p = build_prompt(cat, 5)
        assert "exactly 5" in p and "Deterministic" in p
