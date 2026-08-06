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

from .compare import gradual_guarantee_compare
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


# Ruby snippet: desugar stdin and print the RubyCore AST as JSON (the
# harness↔Lean interface, lib/export.rb). Exit 3 = out of desugar fragment.
_EXPORT_SNIPPET = """\
$LOAD_PATH.unshift(ARGV[0])
require "desugar"
require "export"
src = $stdin.read
begin
  core, = Desugar.program(src)
rescue Desugar::Unsupported => e
  $stderr.puts(e.message)
  exit 3
end
print Export.json(core)
"""


class LeanSUT:
    """The Lean model: desugar -> RubyCore JSON -> `rubycore` executable.

    Two fragment gates compose: the desugar's (exit 3 from the export
    snippet) and the Lean model's own L0 gate (exit 3 from the binary).
    Exit 1 from the binary is a harness/model bug and is surfaced loudly as
    Unsupported with a MODEL-BUG prefix so it is never mistaken for a
    by-design gap.
    """

    name = "lean"

    def __init__(
        self,
        harness_lib: Path | None = None,
        lean_bin: Path | None = None,
        runner: CRubyRunner | None = None,
    ):
        root = Path(__file__).resolve().parents[2]
        self.harness_lib = Path(harness_lib) if harness_lib else root / "harness" / "desugar-dt" / "lib"
        self.lean_bin = Path(lean_bin) if lean_bin else root / "lean" / ".lake" / "build" / "bin" / "rubycore"
        self.runner = runner or CRubyRunner()

    def run(self, source: str) -> Observation | Unsupported:
        proc = subprocess.run(
            [self.runner.ruby, "-e", _EXPORT_SNIPPET, str(self.harness_lib)],
            input=source,
            capture_output=True,
            text=True,
            timeout=self.runner.timeout,
        )
        if proc.returncode == 3:
            return Unsupported(f"out of desugar fragment: {proc.stderr.strip()}")
        if proc.returncode != 0:
            return Unsupported(f"desugar failed: {proc.stderr.strip()[:300]}")
        try:
            lean = subprocess.run(
                [str(self.lean_bin)],
                input=proc.stdout,
                capture_output=True,
                text=True,
                timeout=self.runner.timeout,
            )
        except subprocess.TimeoutExpired:
            return Observation(stdout="", result_repr=None, exception=None, timed_out=True)
        if lean.returncode == 3:
            return Unsupported(f"out of Lean fragment: {lean.stderr.strip()[:300]}")
        if lean.returncode != 0:
            return Unsupported(f"MODEL-BUG: rubycore exit {lean.returncode}: {lean.stderr.strip()[:300]}")
        import json as _json

        try:
            return Observation.from_json(_json.loads(lean.stdout))
        except (ValueError, KeyError) as e:
            return Unsupported(f"MODEL-BUG: unparseable observation: {e}")


class SigStripSUT:
    """The gradual-guarantee probe: CRuby on the *sig-stripped* program.

    A metamorphic SUT — the implementation is not varied, the *program* is. The
    control runs the annotated program, this runs the less-precise variant, and
    the two are related by the gradual guarantee rather than by equality, so it
    carries its own comparator (the `compare` attribute `runner.run_case`
    honors). See `compare.gradual_guarantee_compare` and
    `../docs/semantics/types-and-preservation.md` §C.3 step 1: this is the
    cheapest real check on Sorbet's runtime semantics, and it needs no Lean.
    """

    name = "sig-strip"

    def __init__(self, runner: CRubyRunner | None = None, stripper=None):
        from .sorbet import SigStripper

        self.runner = runner or CRubyRunner()
        self.stripper = stripper or SigStripper(ruby=self.runner.ruby)

    def compare(self, control_obs, sut_obs, case):
        """Custom comparator (see `runner.run_case`): the relation needs a
        *third* run of the annotated program with enforcement neutralized, to
        attribute any difference to runtime checking rather than to the
        annotations themselves. That is why this takes the case, not just the
        two observations."""
        from .sorbet import unchecked_variant

        unchecked = self.runner.run(unchecked_variant(case.source))
        return gradual_guarantee_compare(control_obs, sut_obs, unchecked)

    def run(self, source: str) -> Observation | Unsupported:
        from .sorbet import Unstrippable

        stripped = self.stripper.strip(source)
        if isinstance(stripped, Unstrippable):
            return Unsupported(f"not sig-strippable: {stripped.reason}")
        return self.runner.run(stripped)


def make_sut(kind: str, inject_bug: bool = False) -> SystemUnderTest:
    if kind == "stub":
        return StubSUT()
    if kind == "identity":
        return IdentityCRubySUT()
    if kind == "desugar":
        return DesugarRoundtripSUT(inject_bug=inject_bug)
    if kind == "lean":
        return LeanSUT()
    if kind == "sig-strip":
        return SigStripSUT()
    raise ValueError(f"unknown SUT kind: {kind}")
