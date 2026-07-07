"""Observations and their normalization.

An Observation is what we compare between the control (CRuby) and the system
under test. It mirrors `obs` from docs/semantics/05-differential-testing.md §3,
minus the heap projection (deferred for v1):

    obs = (stdout, result_repr, exception[class, message])

Normalization quotients out legal-but-nondeterministic output (§3.2):
object addresses in `#<Foo:0x...>` inspect strings are rewritten to
allocation-order indices, on every field, on both sides.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, replace

_ADDR_RE = re.compile(r"0x[0-9a-f]{4,}")


@dataclass(frozen=True)
class Observation:
    stdout: str
    result_repr: str | None  # `inspect` of the final value; None if an exception escaped
    exception: tuple[str, str] | None  # (class name, message) or None
    timed_out: bool = False

    def normalized(self) -> "Observation":
        counter: dict[str, str] = {}

        def norm(s: str) -> str:
            def sub(m: re.Match) -> str:
                addr = m.group(0)
                if addr not in counter:
                    counter[addr] = f"<addr{len(counter)}>"
                return counter[addr]

            return _ADDR_RE.sub(sub, s)

        return replace(
            self,
            stdout=norm(self.stdout),
            result_repr=norm(self.result_repr) if self.result_repr is not None else None,
            exception=(self.exception[0], norm(self.exception[1])) if self.exception else None,
        )

    def to_json(self) -> dict:
        return {
            "stdout": self.stdout,
            "result_repr": self.result_repr,
            "exception": list(self.exception) if self.exception else None,
            "timed_out": self.timed_out,
        }

    @classmethod
    def from_json(cls, d: dict) -> "Observation":
        exc = d.get("exception")
        return cls(
            stdout=d["stdout"],
            result_repr=d.get("result_repr"),
            exception=(exc[0], exc[1]) if exc else None,
            timed_out=d.get("timed_out", False),
        )
