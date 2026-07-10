"""Generative campaigns hosted in Hypothesis, with mixed-tier sampling.

The campaign is a Hypothesis property asserting control/SUT agreement; that
buys the shrinker for free (HANDOFF design decision 6). Mixing (HANDOFF
"mixed-tier campaigns", resolution b): the strategy is a weighted choice
between *arms* — "tier1" draws a fresh program from the tier-1 strategies,
corpus arms (e.g. "tier0", "tier3") draw st.sampled_from a persisted corpus.
Tier-1 draws shrink structurally as before; corpus draws shrink only across
the corpus choice, which is fine — corpus cases are already small.

Note: after a disagreement is found, Hypothesis stops generating and shrinks,
so the run ends early — the report flags this. Records produced during the
shrink phase are recorded too (they are real oracle runs), tagged in
provenance with phase="shrink-search".
"""

from __future__ import annotations

import dataclasses
import itertools
from pathlib import Path

from hypothesis import HealthCheck, Phase, given
from hypothesis import seed as hyp_seed
from hypothesis import settings as hyp_settings
from hypothesis import strategies as st

from .compare import CaseResult, Verdict
from .control import CRubyRunner
from .report import Reporter
from .runner import run_case
from .sut import SystemUnderTest
from .testcase import TestCase
from .tiers.tier1.render import render_program
from .tiers.tier1.strategies import programs

WEIGHT_RESOLUTION = 1000  # arm weights are quantized to thousandths


def parse_mix(spec: str) -> dict[str, float]:
    """Parse "tier1=0.99,tier3=0.01" into {"tier1": 0.99, "tier3": 0.01}."""
    mix: dict[str, float] = {}
    for part in spec.split(","):
        name, _, value = part.strip().partition("=")
        if not name or not value:
            raise ValueError(f"bad mix component {part!r} (want name=weight)")
        weight = float(value)
        if weight <= 0:
            raise ValueError(f"mix weight for {name!r} must be > 0, got {weight}")
        if name in mix:
            raise ValueError(f"duplicate mix component {name!r}")
        mix[name] = weight
    return mix


def _thresholds(mix: dict[str, float]) -> list[tuple[str, int]]:
    """Cumulative integer thresholds over [0, WEIGHT_RESOLUTION); every arm
    gets at least one slot so no requested arm is silently dead."""
    total = sum(mix.values())
    arms = list(mix)
    slots = {name: max(1, round(mix[name] / total * WEIGHT_RESOLUTION)) for name in arms}
    # renormalize rounding drift onto the heaviest arm
    drift = WEIGHT_RESOLUTION - sum(slots.values())
    slots[max(arms, key=lambda a: mix[a])] += drift
    out, acc = [], 0
    for name in arms:
        acc += slots[name]
        out.append((name, acc))
    return out


@st.composite
def _mixed_draws(draw, mix: dict[str, float], corpus_cases: dict[str, list[TestCase]],
                 eval_order: bool = False):
    """Draw (arm, payload): payload is a tier-1 AST for the "tier1" arm and a
    corpus TestCase for corpus arms. `eval_order` selects the tier-"1.5" variant of
    the tier-1 generator (probe-wrapped operands); it applies only to pure tier-1
    campaigns, not to mix arms."""
    if list(mix) == ["tier1"]:
        # pure tier 1: no arm-choice draw to shrink over
        return "tier1", draw(programs(eval_order=eval_order))
    r = draw(st.integers(0, WEIGHT_RESOLUTION - 1))
    for name, threshold in _thresholds(mix):
        if r < threshold:
            break
    if name == "tier1":
        return name, draw(programs())
    return name, draw(st.sampled_from(corpus_cases[name]))


class _Disagreement(Exception):
    def __init__(self, result: CaseResult):
        self.result = result
        super().__init__(result.reason)


def run_generative_campaign(
    control: CRubyRunner,
    sut: SystemUnderTest,
    reporter: Reporter,
    n: int,
    seed: int | None = None,
    mix: dict[str, float] | None = None,
    corpus_cases: dict[str, list[TestCase]] | None = None,
    regressions_dir: Path | None = None,
    eval_order: bool = False,
) -> dict:
    mix = mix or {"tier1": 1.0}
    corpus_cases = corpus_cases or {}
    for name in mix:
        if name != "tier1" and not corpus_cases.get(name):
            raise ValueError(f"mix arm {name!r} has no corpus cases loaded")

    counter = itertools.count()
    arm_counts: dict[str, int] = {}
    found_disagreement = False
    pure_tier1 = list(mix) == ["tier1"]

    def prop(drawn):
        nonlocal found_disagreement
        arm, payload = drawn
        i = next(counter)
        phase = "shrink-search" if found_disagreement else "generate"
        if not found_disagreement:
            arm_counts[arm] = arm_counts.get(arm, 0) + 1
        if arm == "tier1":
            case = TestCase(
                id=f"tier1-{i:05d}" if pure_tier1 else f"mix-{i:05d}",
                source=render_program(payload),
                tier=1,
                provenance={"generator": "hypothesis", "arm": arm, "seed": seed,
                            "phase": phase, "eval_order": eval_order},
            )
        else:
            case = dataclasses.replace(
                payload,
                id=f"mix-{i:05d}",
                provenance={**payload.provenance, "arm": arm, "corpus_id": payload.id,
                            "seed": seed, "phase": phase},
            )
        result = run_case(case, control, sut)
        reporter.record(result)
        if result.verdict == Verdict.DISAGREE:
            found_disagreement = True
            raise _Disagreement(result)

    wrapped = given(_mixed_draws(mix, corpus_cases, eval_order))(prop)
    wrapped = hyp_settings(
        max_examples=n,
        deadline=None,
        database=None,
        derandomize=False,
        suppress_health_check=list(HealthCheck),
        phases=[Phase.generate, Phase.shrink],
        print_blob=False,
    )(wrapped)
    if seed is not None:
        wrapped = hyp_seed(seed)(wrapped)

    minimal: CaseResult | None = None
    try:
        wrapped()
    except _Disagreement as e:
        minimal = e.result
    except BaseExceptionGroup as eg:  # hypothesis may group multiple failures
        for sub in eg.exceptions:
            if isinstance(sub, _Disagreement):
                minimal = sub.result
                break
        if minimal is None:
            raise

    extra: dict = {"campaign": {"mix": mix, "requested_examples": n, "seed": seed,
                                "arm_counts": arm_counts, "eval_order": eval_order,
                                "stopped_early_on_disagreement": minimal is not None}}
    if minimal is not None:
        minimal.minimized = True
        reporter.record(minimal)
        origin = minimal.case.provenance.get("arm", "tier1")
        if origin == "tier1" and regressions_dir is not None:
            regressions_dir.mkdir(parents=True, exist_ok=True)
            path = regressions_dir / f"{minimal.case.id}-minimized.rb"
            path.write_text(minimal.case.source)
            extra["campaign"]["minimized_reproducer"] = str(path)
        elif origin != "tier1":
            # corpus cases are already persisted and small; point at the original
            extra["campaign"]["disagreeing_corpus_case"] = minimal.case.provenance["corpus_id"]
    return extra
