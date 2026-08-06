"""The static-oracle two-by-two, and the corpus's declaration gate."""

import pytest

from difftest.sorbet import sorbet_runtime_available, srb_path
from difftest.sorbet_check import CELLS, classify, runtime_kind
from difftest.sources import load_sorbet_corpus

requires_toolchain = pytest.mark.skipif(
    srb_path() is None or not sorbet_runtime_available(),
    reason="Sorbet toolchain not installed",
)


def test_runtime_kind_vocabulary():
    assert runtime_kind(None) == "value"
    assert runtime_kind(("TypeError", "Parameter 'x': Expected type Integer")) == "sorbet_error"
    assert runtime_kind(("NoMethodError", "undefined method 'q'")) == "ruby_error"


@pytest.mark.parametrize(
    "static_ok,kind,exc,cell",
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
    type-family error must be *excluded*. If one ever slips in, the fragment is
    too wide and any theorem stated over it would be false — so this is the
    regression guard that matters most.
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


def test_fragment_checker_classifies_the_hatches():
    from difftest.sorbet import FragmentChecker

    fc = FragmentChecker()
    clean = fc.check(
        '# typed: strict\nrequire "sorbet-runtime"\nextend T::Sig\n'
        "sig { params(x: Integer).returns(String) }\ndef f(x)\n  x.to_s\nend\nputs f(1)\n"
    )
    assert clean is not None and clean.in_fragment, clean

    for source, expected in [
        ("T.unsafe(nil).foo\n", "T.unsafe"),
        ("def g(x)\n  x\nend\n", "g"),
    ]:
        r = fc.check('# typed: true\nrequire "sorbet-runtime"\n' + source)
        assert r is not None and not r.in_fragment
        assert expected in [v["what"] for v in r.violations], r.violations
