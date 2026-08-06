"""Verdicts: the outcome of one test case through the engine."""

from __future__ import annotations

import enum
from dataclasses import dataclass, field

from .observation import Observation
from .testcase import TestCase


class Verdict(enum.Enum):
    AGREE = "agree"
    AGREE_WEAKENED = "agree_weakened"  # relation held, but only via its escape clause
    DISAGREE = "disagree"
    SUT_UNSUPPORTED = "sut_unsupported"  # SUT gated the program out of its fragment
    CONTROL_INVALID = "control_invalid"  # parse error / timeout / nondeterministic under control
    HARNESS_ERROR = "harness_error"  # the engine itself failed to observe


@dataclass
class CaseResult:
    case: TestCase
    verdict: Verdict
    reason: str | None = None  # required for every non-AGREE verdict ("no silent caps")
    control_obs: Observation | None = None
    sut_obs: Observation | None = None
    minimized: bool = False  # True for a shrunk reproducer (tier 1)
    timings: dict = field(default_factory=dict)

    def to_json(self) -> dict:
        return {
            "id": self.case.id,
            "tier": self.case.tier,
            "source": self.case.source,
            "provenance": self.case.provenance,
            "verdict": self.verdict.value,
            "reason": self.reason,
            "control_obs": self.control_obs.to_json() if self.control_obs else None,
            "sut_obs": self.sut_obs.to_json() if self.sut_obs else None,
            "minimized": self.minimized,
            "timings": self.timings,
        }


def compare(control: Observation, sut: Observation) -> tuple[Verdict, str | None]:
    a, b = control.normalized(), sut.normalized()
    if a == b:
        return Verdict.AGREE, None
    # A SUT wall-clock timeout (control completed in time) is inconclusive, not a
    # wrong answer — the model was too slow, it did not disagree. Classify it as
    # out-of-fragment (same neutral bucket as an explicit Unsupported gate). True
    # nontermination is separately caught by the model's step-fuel limit (which
    # exits cleanly as Unsupported), so this only absorbs "correct but too slow".
    if b.timed_out and not a.timed_out:
        return Verdict.SUT_UNSUPPORTED, "sut timeout (too slow; control completed within the limit)"
    # SUT-side dual of the N24 control gate: the SUT overflows the stack on a
    # program the control ran to completion. The desugar roundtrip / model adds a
    # frame per call, so a deep-but-bounded recursion can tip over only on the SUT
    # side. That is a resource-limit artifact of the extra frames, not a wrong
    # answer — inconclusive, same neutral bucket as a SUT timeout. (When the
    # control *also* overflows, run_case already excluded the case as
    # control_invalid before the SUT ran, so this only fires on the asymmetric case.)
    if (b.exception and b.exception[0] == "SystemStackError"
            and not (a.exception and a.exception[0] == "SystemStackError")):
        return Verdict.SUT_UNSUPPORTED, "sut stack overflow (extra frames per call tip a control-terminating program over; inconclusive)"
    parts = []
    if a.stdout != b.stdout:
        parts.append(f"stdout: {a.stdout!r} vs {b.stdout!r}")
    if a.result_repr != b.result_repr:
        parts.append(f"result: {a.result_repr!r} vs {b.result_repr!r}")
    if a.exception != b.exception:
        parts.append(f"exception: {a.exception!r} vs {b.exception!r}")
    if a.timed_out != b.timed_out:
        parts.append(f"timed_out: {a.timed_out} vs {b.timed_out}")
    return Verdict.DISAGREE, " | ".join(parts)


def gradual_guarantee_compare(
    control: Observation, sut: Observation, unchecked: Observation
) -> tuple[Verdict, str | None]:
    """The comparator for the sig-strip probe (`--sut sig-strip`).

    This is not "two implementations should agree" — it is a **metamorphic
    relation** between two *programs*: the control runs the precise (annotated)
    program `e`, the SUT runs the less precise (sig-stripped) `e'`, with
    `e ⊑ e'`. The gradual guarantee (Siek, Vitousek, Cimini & Boyland, SNAPL
    2015; ../docs/semantics/types-and-preservation.md §B.5) predicts that
    changing only the *precision* of annotations does not change behavior,
    except that the more precise program may **trap more errors**.

    The escape clause needs care, and a **third run** to pin down. Stating it as
    "the precise run raised a sorbet-runtime TypeError" is wrong: a program may
    *rescue* its own sig violation (`sig-basic/002` does, and such a program is
    type-safe precisely because the raise never escapes —
    `type-safety-by-reachability.md` §2, "raised != stuck"). Then the two
    variants differ only in stdout, with no exception anywhere to key off. The
    published theorem does not cover this case at all: it is stated over a
    calculus whose blame outcomes cannot be caught and observed.

    So the escape clause is discharged by *attribution* instead, using
    `unchecked` — the annotated program run with sorbet-runtime's enforcement
    neutralized (`sorbet.unchecked_variant`). That isolates exactly one
    variable:

    - control == stripped                        -> AGREE
    - control != stripped, unchecked == stripped -> AGREE_WEAKENED: the whole
      difference is attributable to runtime enforcement firing (licensed —
      the precise program traps more)
    - otherwise                                  -> DISAGREE: the annotations
      changed behavior by something other than trapping, which is what the
      guarantee forbids

    A sorbet-runtime error on the **stripped** side gets its own message but
    the same verdict: stripping removes checks, so a variant that blames where
    the original did not falsifies the guarantee outright (structural
    constructs that could still raise are gated out by the stripper, so this
    cannot fire spuriously).
    """
    a, b, u = control.normalized(), sut.normalized(), unchecked.normalized()
    if a == b:
        return Verdict.AGREE, None
    if b.timed_out and not a.timed_out:
        return Verdict.SUT_UNSUPPORTED, "stripped variant timed out (inconclusive)"

    from .sorbet import is_sorbet_runtime_error

    if u == b:
        trapped = (
            f"{a.exception[0]}: {a.exception[1].splitlines()[0][:120]}"
            if is_sorbet_runtime_error(a.exception)
            else "trapped internally (rescued by the program; visible only in stdout)"
        )
        return Verdict.AGREE_WEAKENED, (
            "difference fully attributable to runtime enforcement — with "
            f"enforcement neutralized the annotated program matches the stripped one [{trapped}]"
        )
    if is_sorbet_runtime_error(b.exception):
        return Verdict.DISAGREE, (
            "GUARANTEE VIOLATION: the sig-stripped variant blames where the "
            f"annotated one did not: {b.exception!r}"
        )
    parts = [f"unchecked: {u.to_json()}"]
    if a.stdout != b.stdout:
        parts.append(f"stdout: {a.stdout!r} vs {b.stdout!r}")
    if a.result_repr != b.result_repr:
        parts.append(f"result: {a.result_repr!r} vs {b.result_repr!r}")
    if a.exception != b.exception:
        parts.append(f"exception: {a.exception!r} vs {b.exception!r}")
    return Verdict.DISAGREE, "GUARANTEE VIOLATION: " + " | ".join(parts)
