"""Test cases: a Ruby program plus where it came from."""

from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class TestCase:
    id: str
    source: str  # Ruby program text
    tier: int  # 0..3 (which generation tier produced it)
    provenance: dict = field(default_factory=dict, compare=False)
