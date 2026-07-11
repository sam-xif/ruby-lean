"""Tier "1.5": the tier-1 generator + eval-order probes.

Deliberately thin — it owns no grammar of its own. `programs()` is the shared
tier-1 program strategy with the eval-order probe transform composed on via
`.map`, so all generation logic stays in one place (`..tier1.strategies`) and
tier 1.5 differs only by the post-generation transform (`probe.py`). `.map` keeps
shrinking intact: Hypothesis shrinks the underlying tier-1 AST and re-applies the
pure transform.
"""

from __future__ import annotations

from ..tier1.strategies import programs as _tier1_programs
from .probe import add_eval_order_probes


def programs():
    """The tier-1.5 program strategy (tier-1 programs, probe-wrapped)."""
    return _tier1_programs().map(add_eval_order_probes)
