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


# --------------------------------------------------------------------------
# sig-stripping (the precision transform)
# --------------------------------------------------------------------------


@pytest.fixture(scope="module")
def stripper():
    from difftest.sorbet import SigStripper

    return SigStripper()


def test_strips_sig_and_extend(stripper):
    out = stripper.strip(CLEAN)
    assert "sig" not in out
    assert "T::Sig" not in out
    assert "def f(x)" in out and "x.to_s" in out


def test_strips_assertion_family(stripper):
    out = stripper.strip(
        '# typed: true\nrequire "sorbet-runtime"\n'
        "a = T.let(1, Integer)\n"
        "b = T.cast(a, Integer)\n"
        "c = T.must(b)\n"
        "d = T.unsafe(c)\n"
        "puts a + b + c + d\n"
    )
    assert "T." not in out
    assert "a = 1" in out and "b = a" in out and "c = b" in out and "d = c" in out


def test_strips_nested_assertions_to_a_fixpoint(stripper):
    out = stripper.strip(
        '# typed: true\nrequire "sorbet-runtime"\n'
        "x = T.must(T.cast(T.unsafe(1), Integer))\n"
    )
    assert "x = 1" in out


def test_strips_chained_checked_sig(stripper):
    out = stripper.strip(
        '# typed: true\nrequire "sorbet-runtime"\nextend T::Sig\n'
        "sig { params(x: Integer).returns(String).checked(:never) }\n"
        "def label(x)\n  x.to_s\nend\nputs label(1)\n"
    )
    assert "sig" not in out and "checked" not in out
    assert "def label(x)" in out


def test_require_is_kept(stripper):
    # The two variants must differ only in annotation precision, so the require
    # (which changes what is loaded) is deliberately left in place.
    runnable = CLEAN.replace(
        "# typed: strict\n", '# typed: strict\nrequire "sorbet-runtime"\n'
    )
    assert 'require "sorbet-runtime"' in stripper.strip(runnable)


def test_structural_constructs_are_gated_not_mangled(stripper):
    from difftest.sorbet import Unstrippable

    out = stripper.strip(
        '# typed: true\nrequire "sorbet-runtime"\n'
        "class Point < T::Struct\n  const :x, Integer\nend\n"
        "puts Point.new(x: 1).x\n"
    )
    assert isinstance(out, Unstrippable)
    assert "T::Struct" in out.reason


def test_stripped_program_still_runs(stripper):
    from difftest.control import CRubyRunner

    out = stripper.strip(CLEAN)
    obs = CRubyRunner().run(out)
    assert obs.exception is None, obs.exception
    assert obs.stdout == "3\n"


def test_strips_correctly_with_non_ascii_earlier_in_the_file(stripper):
    """Prism reports **byte** offsets; the splices index by **character**.

    A single multi-byte character anywhere before an edit desynchronizes the
    two and silently corrupts the output — the stripper produced
    `"ig { returns(Integer) }"` (two characters eaten) before this was fixed.
    Non-ASCII in comments is ordinary in this corpus, so the guard is cheap.
    """
    out = stripper.strip(
        "# typed: true\n"
        'require "sorbet-runtime"\n'
        "extend T::Sig\n"
        "\n"
        "# a section marker — § — two bytes, one character\n"
        "sig { params(x: Integer).returns(String) }\n"
        "def f(x)\n"
        "  x.to_s\n"
        "end\n"
        "puts f(1)\n"
    )
    assert "sig {" not in out and "T::Sig" not in out
    assert "def f(x)\n  x.to_s\nend" in out, out
    assert "§" in out  # the comment itself survives untouched
