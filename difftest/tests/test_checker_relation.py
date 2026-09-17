"""The pinned zeros must actually fire.

A harness that reports all-zero because it never triggers is worse than no
harness: it reads as evidence. These tests are the guard on the guard — each
one drives `relate` into a cell and, for the three pinned zeros, asserts the
cell is reachable at all.

Spec: `difftest/checker_relation.py`'s module docstring.
"""

from dataclasses import dataclass

from difftest.checker_relation import (
    CHECK_CELLS,
    EXCLUDED_CODES,
    PINNED_ZERO_CELLS,
    excluded,
    relate,
    type_relevant,
)

FAMILY = ("NoMethodError", "ArgumentError", "TypeError")


@dataclass(frozen=True)
class E:
    """Stand-in for sorbet.StaticError — only `.code` is consulted."""

    code: int | None


def rel(verdict, errors=(), exc=None):
    return relate(verdict, list(errors), exc, FAMILY)


# --------------------------------------------------------------------------
# The three pinned zeros are reachable
# --------------------------------------------------------------------------


def test_accept_with_type_relevant_error_is_a_violation():
    assert rel("accept", [E(7002)]) == "check-accept-disagreement"


def test_reject_with_no_error_at_all_is_a_violation():
    assert rel("reject", []) == "check-reject-disagreement"


def test_accept_with_cruby_type_error_is_a_model_bug():
    assert rel("accept", [], exc="TypeError") == "check-model-bug"


def test_every_pinned_zero_is_reachable():
    """Guards against a future refactor making a zero unreachable, which would
    silently retire it while leaving it in the report as a reassuring 0."""
    reached = {
        rel("accept", [E(7002)]),
        rel("reject", []),
        rel("accept", [], exc="TypeError"),
    }
    assert set(PINNED_ZERO_CELLS) <= reached


# --------------------------------------------------------------------------
# The exclusion list, and why it must default the other way
# --------------------------------------------------------------------------


def test_excluded_codes_do_not_break_accept():
    """`if true then 1 else 2 end`: we accept, srb says 7006. Benign — this is
    the case that forces the exclusion list to exist (§7.1)."""
    assert rel("accept", [E(7006)]) == "check-accept-agrees"
    assert rel("accept", [E(3002)]) == "check-accept-agrees"


def test_unclassified_code_is_treated_as_type_relevant():
    """The safety property of the module. A diagnostic nobody has classified
    must fire the zero, not be absorbed. If this test ever fails, the module has
    been inverted into an allowlist and disagreements can hide in it."""
    unseen = 9999
    assert unseen not in EXCLUDED_CODES
    assert rel("accept", [E(unseen)]) == "check-accept-disagreement"


def test_missing_code_is_type_relevant():
    """srb lines without a parsed code (`code is None`) count too — the same
    default, for the same reason."""
    assert rel("accept", [E(None)]) == "check-accept-disagreement"


def test_partition_is_total():
    errs = [E(7002), E(7006), E(None), E(3002)]
    assert len(type_relevant(errs)) + len(excluded(errs)) == len(errs)


# --------------------------------------------------------------------------
# Agreement on the verdict is not agreement on the reason (§7.2)
# --------------------------------------------------------------------------


def test_reject_agreeing_only_via_an_excluded_code_is_recorded_separately():
    """`if false then 1 + nil else 0 end`: we reject for `1 + nil`, srb rejects
    for unreachability. Not a failure, but not a win — it must not be counted as
    agreement on the reason."""
    assert rel("reject", [E(7006)]) == "check-reject-agrees-verdict-only"


def test_reject_agreeing_on_a_type_error_is_agreement_on_the_reason():
    assert rel("reject", [E(7002)]) == "check-reject-agrees-reason"


def test_reject_with_mixed_codes_counts_as_agreement_on_the_reason():
    assert rel("reject", [E(7006), E(7002)]) == "check-reject-agrees-reason"


# --------------------------------------------------------------------------
# Abstention, and the pipeline/abstention distinction
# --------------------------------------------------------------------------


def test_unknown_never_violates_anything():
    """Incompleteness is the expected state of a growing checker: srb may reject
    while we abstain, and that must never fail the run."""
    for errors in ([], [E(7002)], [E(7006)]):
        for exc in (None, "TypeError"):
            assert rel("unknown", errors, exc) == "check-unknown"


def test_undecidable_is_not_unknown():
    """Pipeline breakage must not read as honest abstention, or the ratchet
    flatters itself."""
    assert rel(None, [E(7002)]) == "check-undecidable"
    assert "check-undecidable" not in PINNED_ZERO_CELLS


def test_model_bug_outranks_accept_disagreement():
    """Both are real; a model disagreeing with CRuby invalidates the ground the
    checker stands on, so it is reported first."""
    assert rel("accept", [E(7002)], exc="TypeError") == "check-model-bug"


# --------------------------------------------------------------------------
# Report integrity
# --------------------------------------------------------------------------


def test_every_cell_relate_can_return_is_documented():
    produced = {
        rel("accept", []),
        rel("accept", [E(7002)]),
        rel("accept", [], exc="TypeError"),
        rel("reject", []),
        rel("reject", [E(7002)]),
        rel("reject", [E(7006)]),
        rel("unknown", []),
        rel(None, []),
    }
    assert produced <= set(CHECK_CELLS)
    # and the documented set has no dead entries
    assert produced == set(CHECK_CELLS)
