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
