"""Registry of generative tiers — arm name -> program-strategy factory.

Generative arms produce a tier-1 AST (rendered to source); corpus arms
(tier0/tier3) sample a persisted corpus and are handled separately in the CLI.
Adding a new generative tier is a one-line entry here: both pure `--tier` runs
and `--mix` campaigns pick it up automatically.
"""

from .tier1.strategies import programs as _tier1
from .tier1_5.strategies import programs as _tier1_5

GENERATIVE_ARMS = {
    "tier1": _tier1,
    "tier1.5": _tier1_5,
}
