"""The relation between our static checker and `srb` — and its pinned zeros.

Soundness of `accept` was *proved*, so difftesting does not test it. What the
comparison buys is **relevance**: evidence that `check` formalizes *Sorbet*
rather than a type system we invented.

    accept  =>  srb reports no error in a type-relevant class
    reject  =>  srb reports some error, in any class

The asymmetry is deliberate and forced. `accept` is the strong claim, so it gets
the strong test. `reject` claims only that our rules refute the program, so it
gets the weak one — and it *must* be the weak one, because our dead-branch
rejects are witnessed by `srb` only through 7006.

Failures the other way — `srb` rejects and we say `unknown` — are
**incompleteness**, the expected state of a growing checker, and are counted
rather than failed.
"""

from __future__ import annotations

# ---------------------------------------------------------------------------
# Which srb diagnostics are about types
# ---------------------------------------------------------------------------

# Codes deliberately NOT treated as type errors. Each entry was found by
# measurement over the bootstraptest corpus, not anticipated. Adding
# to this list is a real decision — it narrows what the accept zero can catch —
# so each needs a reason recorded here.
EXCLUDED_CODES: dict[int, str] = {
    7006: (
        "unreachable code / left side of `&&` was always truthy — a "
        "reachability opinion, not a type one. The program is well typed; srb "
        "is reporting that a branch cannot run. We have no reachability "
        "analysis and claim none."
    ),
    3002: (
        "unsupported integer literal (bignum) — an srb implementation limit, "
        "not a statement about the program's types."
    ),
}

# Everything else counts as type-relevant, INCLUDING codes never seen before.
# That default is the whole safety property of this module: an unclassified srb
# diagnostic on an accepted program fires the accept zero and stops the run,
# rather than being quietly absorbed. The alternative — an allowlist of known
# type-relevant codes, unknown ones ignored — turns this file into a place to
# park disagreements, which is the erosion the zeros exist to prevent.


def type_relevant(errors) -> list:
    """The srb errors that bear on typing."""
    return [e for e in errors if e.code not in EXCLUDED_CODES]


def excluded(errors) -> list:
    """The srb errors deliberately not counted, kept visible in the report so
    the exclusions stay under review rather than becoming invisible."""
    return [e for e in errors if e.code in EXCLUDED_CODES]


# ---------------------------------------------------------------------------
# The cells
# ---------------------------------------------------------------------------

# Order matters: the three pinned zeros first, so a report reads worst-first.
CHECK_CELLS: dict[str, str] = {
    "check-model-bug": (
        "check accepted; CRuby raised a type-family error. Cannot be a checker "
        "bug — check_sound is proved — so the Lean model and CRuby disagree"
    ),
    "check-accept-disagreement": (
        "check accepted; srb reported a type-relevant error. We over-claim, or "
        "we found an srb bug"
    ),
    "check-reject-disagreement": (
        "check rejected; srb reported no error at all. Our reject rule "
        "over-claims — downgrade it to unknown"
    ),
    "check-accept-agrees": "check accepted; srb clean of type-relevant errors",
    "check-reject-agrees-reason": (
        "check rejected; srb reported a type-relevant error too — agreement on "
        "the reason"
    ),
    "check-reject-agrees-verdict-only": (
        "check rejected; srb erred only on excluded codes — agreement on the "
        "verdict by coincidence, worth watching (§7.2)"
    ),
    "check-unknown": "check abstained; no claim, and none tested",
    "check-undecidable": "did not desugar/decode — not the same as `unknown`",
}

# The cells that fail the run.
PINNED_ZERO_CELLS = (
    "check-model-bug",
    "check-accept-disagreement",
    "check-reject-disagreement",
)


def relate(
    verdict: str | None,
    static_errors,
    exc_class: str | None,
    type_error_family: tuple[str, ...],
) -> str:
    """Classify one program into a `CHECK_CELLS` key.

    **`verdict` is the epistemic reading — `CheckResultLean.verdict`, not
    `.decision`.** D12 made the reported decision total (`accept`/`reject`, never
    `unknown`); this function must keep seeing the three-valued basis, because its
    `check-reject-disagreement` cell is the pinned zero for *our rules refute this
    program* and a `reject` that merely means *not certified* has no such
    obligation. Feeding `.decision` in here would turn every abstention into a
    violation and the pinned zero into noise. `sorbet.py`'s docstring has the
    table.

    `verdict is None` means the pipeline could not produce one.

    Precedence note: on an `accept` where CRuby raised a type-family error *and*
    srb also complained, `check-model-bug` wins. Both are real, but a model that
    disagrees with CRuby invalidates the ground the checker stands on, so it is
    the one to look at first.
    """
    if verdict is None:
        return "check-undecidable"
    if verdict == "accept":
        if exc_class in type_error_family:
            return "check-model-bug"
        return (
            "check-accept-disagreement"
            if type_relevant(static_errors)
            else "check-accept-agrees"
        )
    if verdict == "reject":
        if not static_errors:
            return "check-reject-disagreement"
        return (
            "check-reject-agrees-reason"
            if type_relevant(static_errors)
            else "check-reject-agrees-verdict-only"
        )
    return "check-unknown"
