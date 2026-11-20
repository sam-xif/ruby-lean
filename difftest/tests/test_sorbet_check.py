"""The static-oracle two-by-two, and the corpus's declaration gate."""

import pytest
from difftest.sorbet import FragmentChecker, sorbet_runtime_available, srb_path
from difftest.sorbet_check import CELLS, classify, runtime_kind
from difftest.sources import load_sorbet_corpus

requires_toolchain = pytest.mark.skipif(
    srb_path() is None or not sorbet_runtime_available(),
    reason="Sorbet toolchain not installed",
)

# `FragmentChecker` shells out to the Lean-built `rubycore` binary, which the
# fast `difftest` CI job does not build (`lean-gate` owns that build). Skip
# rather than fail with FileNotFoundError when the model is not built.
requires_rubycore = pytest.mark.skipif(
    not FragmentChecker().lean_bin.exists(),
    reason="Lean rubycore binary not built",
)

# A `sig`-annotated method in a class body, the declaration a displacing
# `define_method` below it would replace.
SIG_ANNOTATED_F = (
    "class C\n  extend T::Sig\n"
    "  sig { params(x: Integer).returns(String) }\n  def f(x)\n    x.to_s\n  end\n"
)
SIG_ANNOTATED_SELF_F = (
    "class C\n  extend T::Sig\n"
    "  sig { params(x: Integer).returns(String) }\n  def self.f(x)\n    x.to_s\n  end\n"
)


def test_runtime_kind_vocabulary():
    assert runtime_kind(None) == "value"
    assert runtime_kind(("TypeError", "Parameter 'x': Expected type Integer")) == "sorbet_error"
    assert runtime_kind(("NoMethodError", "undefined method 'q'")) == "ruby_error"


@pytest.mark.parametrize(
    ("static_ok", "kind", "exc", "cell"),
    [
        (True, "value", None, "accepted-and-safe"),
        (True, "sorbet_error", "TypeError", "accepted-blamed"),
        (True, "ruby_error", "NoMethodError", "unsoundness-witness"),
        (True, "ruby_error", "TypeError", "unsoundness-witness"),
        (True, "ruby_error", "ArgumentError", "unsoundness-witness"),
        # not a type error: Sorbet never claimed to prevent it
        (True, "ruby_error", "ZeroDivisionError", "accepted-nontype-error"),
        # a bare NameError is deliberately outside the family (an undefined
        # constant is not a type error) — matching the Lean typeErrorFamily
        (True, "ruby_error", "NameError", "accepted-nontype-error"),
        (False, "value", None, "conservative-rejection"),
        (False, "ruby_error", "NoMethodError", "rejected-and-unsafe"),
        (False, "sorbet_error", "TypeError", "rejected-and-blamed"),
    ],
)
def test_classification(static_ok, kind, exc, cell):
    assert classify(static_ok, kind, exc) == cell
    assert cell in CELLS


@requires_toolchain
def test_corpus_matches_its_declarations(tmp_path):
    """Every sidecar's declared (static, runtime) pair is what actually happens.

    This is the corpus's integrity gate: the declarations are checked, not
    decorative, so a Sorbet version bump that changes a verdict fails loudly
    instead of quietly invalidating the taxonomy.
    """
    from difftest.sorbet_check import run_check

    summary = run_check(load_sorbet_corpus(), tmp_path)
    assert summary["mismatches"] == []
    # the corpus exists to hold findings; if these ever empty out, the
    # off-diagonal programs stopped being off-diagonal and want re-triage
    assert summary["unsoundness_witnesses"]
    assert summary["conservative_rejections"]


# --------------------------------------------------------------------------
# the fragment: the scope a soundness theorem could have
# --------------------------------------------------------------------------


@requires_toolchain
def test_no_unsoundness_witness_is_in_the_fragment(tmp_path):
    """The load-bearing property of the fragment definition.

    Every program that Sorbet accepts and that nonetheless reaches an uncaught
    type-family error must be *excluded* from what a theorem claims. If one
    ever slips in, any theorem stated over it would be false — so this is the
    regression guard that matters most.

    D10 (`RubyCore/Sorbet/Fragment.lean`) admits a method *addition* and, with
    one syntactic exception, a method *redefinition*: a `define_method` over a
    `sig`-annotated name in the same body displaces that declaration without
    anything checking the replacement conforms, so the fragment refuses it.
    Every witness must therefore be outside the fragment, with no exception —
    a new witness landing in it fails this test.
    """
    from difftest.sorbet_check import run_check

    summary = run_check(load_sorbet_corpus(), tmp_path)
    witnesses = set(summary["unsoundness_witnesses"])
    assert witnesses, "corpus lost its witnesses; the guard is now vacuous"
    assert witnesses & set(summary["in_fragment"]) == set()


@requires_toolchain
def test_theorem_scope_is_fragment_intersect_accepted(tmp_path):
    from difftest.sorbet_check import run_check

    summary = run_check(load_sorbet_corpus(), tmp_path)
    assert set(summary["theorem_scope"]) <= set(summary["in_fragment"])
    assert summary["theorem_scope"], "nothing in scope — a theorem would be vacuous"


@requires_rubycore
def test_fragment_checker_classifies_the_hatches():
    from difftest.sorbet import FragmentChecker

    fc = FragmentChecker()
    clean = fc.check(
        '# typed: strict\nrequire "sorbet-runtime"\nextend T::Sig\n'
        "sig { params(x: Integer).returns(String) }\ndef f(x)\n  x.to_s\nend\nputs f(1)\n"
    )
    assert clean is not None
    assert clean.in_fragment, clean

    for source, expected in [
        ("T.unsafe(nil).foo\n", "T.unsafe"),
        ("def g(x)\n  x\nend\n", "g"),
        (
            SIG_ANNOTATED_F + "  define_method(:f) { |x| x.no_such_method }\nend\n",
            "define_method :f",
        ),
        # The explicit-Proc form installs the same name as the block form, so the
        # match must not require a one-element argument list.
        (
            SIG_ANNOTATED_F + "  define_method(:f, proc { |x| x.no_such_method })\nend\n",
            "define_method :f",
        ),
        # Same hazard on the singleton table.
        (
            SIG_ANNOTATED_SELF_F
            + "  define_singleton_method(:f, proc { |x| x.no_such_method })\nend\n",
            "define_singleton_method :f",
        ),
        # `attr_*` declares the names it generates, so replacing one is the same
        # displacing redefinition. The writer an accessor generates is `name=`.
        (
            (
                "class C\n  extend T::Sig\n  sig { returns(String) }\n"
                "  attr_reader :name\n  define_method(:name) { 1 }\nend\n"
            ),
            "define_method :name",
        ),
        (
            (
                "class C\n  extend T::Sig\n  sig { returns(String) }\n"
                "  attr_accessor :name\n  define_method(:name=) { |v| v }\nend\n"
            ),
            "define_method :name=",
        ),
    ]:
        r = fc.check('# typed: true\nrequire "sorbet-runtime"\n' + source)
        assert r is not None
        assert not r.in_fragment
        assert expected in [v["what"] for v in r.violations], r.violations


@requires_rubycore
def test_fragment_checker_admits_a_non_displacing_define_method():
    """D10 still admits a redefinition the declarations cannot see.

    The exclusion is narrow on purpose: only a literal `define_method` over a
    name a `sig` in the *same* body declares is refused. A `define_method`
    installing a name nothing annotated, one whose name is computed rather than
    literal, and one that displaces a `def` with no `sig` (outside the fragment
    for its own reason) stay admitted — refusing them would exclude ordinary
    Ruby without buying any soundness.
    """
    from difftest.sorbet import FragmentChecker

    fc = FragmentChecker()
    for source in [
        SIG_ANNOTATED_F + "  define_method(:g) { |x| x }\nend\n",
        SIG_ANNOTATED_F + "  name = :f\n  define_method(name) { |x| x }\nend\n",
    ]:
        r = fc.check('# typed: true\nrequire "sorbet-runtime"\n' + source)
        assert r is not None
        assert r.in_fragment, (source, r.violations)
