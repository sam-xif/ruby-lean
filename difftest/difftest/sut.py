"""The system under test (SUT) interface and reference implementations.

The engine is deliberately not coupled to any particular modeling approach:
a SUT is anything that can take a Ruby source string and either produce an
Observation or declare the program outside its supported fragment.

The eventual Lean-semantics executable plugs in here by implementing `run`.
"""

from __future__ import annotations

import os
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Protocol, runtime_checkable

from .control import CRubyRunner
from .observation import Observation


@dataclass(frozen=True)
class Unsupported:
    """The SUT declares the program outside its modeled fragment (with a reason)."""

    reason: str


@runtime_checkable
class SystemUnderTest(Protocol):
    name: str

    def run(self, source: str) -> Observation | Unsupported: ...


class StubSUT:
    """Placeholder for the future Lean model: supports nothing yet.

    A campaign against the stub still exercises the whole engine (generation,
    control runs, determinism filter, reporting) — every case lands in
    SUT_UNSUPPORTED.
    """

    name = "stub"

    def run(self, source: str) -> Observation | Unsupported:
        return Unsupported("stub SUT: no model attached yet")


class IdentityCRubySUT:
    """CRuby itself as the SUT — a pipeline smoke test that must always AGREE."""

    name = "identity"

    def __init__(self, runner: CRubyRunner | None = None):
        self.runner = runner or CRubyRunner()

    def run(self, source: str) -> Observation | Unsupported:
        return self.runner.run(source)


# Ruby snippet that desugars stdin through the existing desugar-dt harness and
# prints the rendered RubyCore. Exit 3 = out of fragment (clean gate).
_DESUGAR_SNIPPET = """\
$LOAD_PATH.unshift(ARGV[0])
require "desugar"
require "render"
src = $stdin.read
begin
  core, = Desugar.program(src, inject_bug: ENV["DESUGAR_BUG"] == "1")
rescue Desugar::Unsupported => e
  $stderr.puts(e.message)
  exit 3
end
print Render.core(core)
"""


class DesugarRoundtripSUT:
    """Adapter over the existing desugar-dt harness: desugar -> render -> CRuby.

    This is a real, available-today SUT: it models Ruby as "the desugared
    program's behavior under CRuby". With inject_bug=True (DESUGAR_BUG) the
    harness's known-buggy &&/|| desugaring produces genuine disagreements,
    which validates the engine's detection + minimization end to end.
    """

    name = "desugar"

    def __init__(
        self,
        harness_lib: Path | None = None,
        runner: CRubyRunner | None = None,
        inject_bug: bool = False,
    ):
        default = Path(__file__).resolve().parents[2] / "harness" / "desugar-dt" / "lib"
        self.harness_lib = Path(harness_lib) if harness_lib else default
        self.runner = runner or CRubyRunner()
        self.inject_bug = inject_bug

    def run(self, source: str) -> Observation | Unsupported:
        env = {**os.environ}
        if self.inject_bug:
            env["DESUGAR_BUG"] = "1"
        proc = subprocess.run(
            [self.runner.ruby, "-e", _DESUGAR_SNIPPET, str(self.harness_lib)],
            input=source,
            capture_output=True,
            text=True,
            timeout=self.runner.timeout,
            env=env,
        )
        if proc.returncode == 3:
            return Unsupported(f"out of desugar fragment: {proc.stderr.strip()}")
        if proc.returncode != 0:
            return Unsupported(f"desugar failed: {proc.stderr.strip()[:300]}")
        return self.runner.run(proc.stdout)


def make_sut(kind: str, inject_bug: bool = False) -> SystemUnderTest:
    if kind == "stub":
        return StubSUT()
    if kind == "identity":
        return IdentityCRubySUT()
    if kind == "desugar":
        return DesugarRoundtripSUT(inject_bug=inject_bug)
    raise ValueError(f"unknown SUT kind: {kind}")
