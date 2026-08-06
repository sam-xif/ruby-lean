import pytest

from difftest.sorbet import (
    SorbetStatic,
    is_sorbet_runtime_error,
    sorbet_runtime_available,
    srb_path,
)

requires_srb = pytest.mark.skipif(srb_path() is None, reason="srb not installed")
requires_runtime = pytest.mark.skipif(
    not sorbet_runtime_available(), reason="sorbet-runtime gem not installed"
)


CLEAN = """\
# typed: strict
extend T::Sig

sig { params(x: Integer).returns(String) }
def f(x)
  x.to_s
end

puts f(3)
"""

ILL_TYPED = CLEAN + 'puts f("nope")\n'


@pytest.fixture(scope="module")
def static():
    return SorbetStatic()


@requires_srb
def test_clean_program_has_no_errors(static):
    result = static.check(CLEAN)
    assert result.ok, result.raw
    assert result.errors == ()


@requires_srb
def test_ill_typed_program_reports_a_located_coded_error(static):
    result = static.check(ILL_TYPED)
    assert not result.ok
    assert len(result.errors) == 1
    (err,) = result.errors
    assert err.line == 10  # the `f("nope")` call site
    assert err.code == 7002  # srb.help/7002 — argument type mismatch
    assert "Integer" in err.message


@requires_srb
def test_untyped_sigil_suppresses_the_error(static):
    # `# typed: false` is the default strictness: only syntax/constant/sig-shape
    # errors are reported, so the same program is accepted (§A.4).
    result = static.check(ILL_TYPED.replace("# typed: strict", "# typed: false"))
    assert result.ok, result.raw


@requires_runtime
def test_runtime_sig_violation_is_classified(tmp_path):
    from difftest.control import CRubyRunner

    obs = CRubyRunner().run(
        'require "sorbet-runtime"\n'
        "class A\n"
        "  extend T::Sig\n"
        "  sig { params(x: Integer).returns(String) }\n"
        "  def f(x); x.to_s; end\n"
        "end\n"
        'A.new.f("nope")\n'
    )
    assert obs.exception is not None
    assert obs.exception[0] == "TypeError"
    assert is_sorbet_runtime_error(obs.exception)


def test_genuine_typeerror_is_not_classified_as_sorbet():
    # The discriminator must not swallow Ruby's own TypeErrors — they are the
    # `typeStuck` family the reachability checker cares about.
    assert not is_sorbet_runtime_error(
        ("TypeError", "String can't be coerced into Integer")
    )
    assert not is_sorbet_runtime_error(("NoMethodError", "undefined method 'x'"))
    assert not is_sorbet_runtime_error(None)
