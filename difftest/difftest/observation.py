"""Observations and their normalization.

An Observation is what we compare between the control (CRuby) and the system
under test. It mirrors `obs` from README.md §Methodology (artifact 05 §3),
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

# sorbet-runtime appends source locations to every enforcement error:
#
#   Parameter 'x': Expected type Integer, got type String with value "two"
#   Caller: prog.rb:19
#   Definition: prog.rb:14 (Object#stringify)
#
# RubyCore carries no line numbers — the desugared AST has no source positions
# by design — so a model can never reproduce these lines. They are dropped from
# **exception messages only**, and only when the line has exactly this shape.
# Deliberately not applied to stdout: a program that prints an exception message
# itself would then have real output quotiented away, and the narrow rule keeps
# the risk of manufacturing a false AGREE confined to text neither side can
# meaningfully differ on.
_LOCATION_LINE_RE = re.compile(r"^(?:Caller|Definition): .*$\n?", re.MULTILINE)


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
            exception=(
                (self.exception[0], _LOCATION_LINE_RE.sub("", norm(self.exception[1])).rstrip("\n"))
                if self.exception
                else None
            ),
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
