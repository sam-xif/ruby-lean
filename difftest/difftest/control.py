"""The control: run a Ruby program under CRuby and produce an Observation.

The program is spliced textually into a wrapper (the "harness prelude",
05-differential-testing §3.1) that captures $stdout into a StringIO, rescues
every Exception (including SystemExit) as (class, message), inspects the final
value, and emits a JSON observation on the real stdout behind a sentinel.

Known v1 limitations (documented, not silent): writes to the STDOUT constant
bypass the $stdout capture; programs that collide with the __difftest_*
wrapper locals or redefine JSON/StringIO internals can break the wrapper
(reported as a harness error, never as agreement).
"""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
from functools import lru_cache
from pathlib import Path

from .observation import Observation

SENTINEL = "\n__DIFFTEST_OBS__"

_WRAPPER = """\
require "stringio"
require "json"
__difftest_real_stdout = STDOUT.dup
$stdout = StringIO.new
__difftest_exc = nil
__difftest_result = nil
begin
  __difftest_result = begin
{program}
  end
rescue ::Exception => __difftest_e
  __difftest_exc = __difftest_e
end
__difftest_obs = {{
  "stdout" => $stdout.string,
  "result_repr" => __difftest_exc ? nil : (begin; __difftest_result.inspect; rescue ::Exception; "<uninspectable>"; end),
  "exception" => __difftest_exc && [__difftest_exc.class.name.to_s, (begin; __difftest_exc.message.to_s; rescue ::Exception; "<unmessageable>"; end)],
}}
__difftest_real_stdout.write({sentinel} + JSON.generate(__difftest_obs))
"""


def _scrub_program_path(obs: Observation, path: str) -> Observation:
    """Rewrite the wrapper's own temp-file path out of the observation.

    The engine writes each program to a fresh `tmpXXXX.rb`, so anything that
    reports the script path — `__FILE__`, a backtrace, and notably every
    sorbet-runtime error message ("Caller: /var/…/tmpshj155fk.rb:19") — differs
    between two runs of the *same* program. That is nondeterminism the harness
    injected, not the program's, and left alone it makes the determinism
    double-run reject every program whose sig check fires. Quotienting out our
    own path is the honest fix; genuine nondeterminism is still caught.
    (`os.path.realpath` too: on macOS /var is a symlink to /private/var, and
    Ruby reports the resolved form.)
    """
    variants = {path, os.path.realpath(path)}

    def scrub(s: str) -> str:
        for v in variants:
            s = s.replace(v, "<program>")
        return s

    return Observation(
        stdout=scrub(obs.stdout),
        result_repr=scrub(obs.result_repr) if obs.result_repr is not None else None,
        exception=(obs.exception[0], scrub(obs.exception[1])) if obs.exception else None,
        timed_out=obs.timed_out,
    )


class HarnessError(Exception):
    """The wrapper itself failed to produce an observation (not a verdict on the program)."""


@lru_cache(maxsize=1)
def ruby_path() -> str:
    """Resolve the pinned CRuby. DIFFTEST_RUBY overrides; default is Homebrew ruby."""
    env = os.environ.get("DIFFTEST_RUBY")
    if env:
        return env
    try:
        prefix = subprocess.run(
            ["brew", "--prefix", "ruby"], capture_output=True, text=True, check=True
        ).stdout.strip()
        candidate = Path(prefix) / "bin" / "ruby"
        if candidate.exists():
            return str(candidate)
    except (subprocess.CalledProcessError, FileNotFoundError):
        pass
    return "ruby"


class CRubyRunner:
    def __init__(self, ruby: str | None = None, timeout: float = 10.0):
        self.ruby = ruby or ruby_path()
        self.timeout = timeout

    def check_parses(self, source: str) -> str | None:
        """Return None if the program parses, else the syntax error text."""
        proc = subprocess.run(
            [self.ruby, "-c", "-"],
            input=source,
            capture_output=True,
            text=True,
            timeout=self.timeout,
        )
        return None if proc.returncode == 0 else proc.stderr.strip()

    def run(self, source: str) -> Observation:
        wrapped = _WRAPPER.format(program=source, sentinel=json.dumps(SENTINEL))
        with tempfile.NamedTemporaryFile("w", suffix=".rb", delete=False) as f:
            f.write(wrapped)
            path = f.name
        try:
            # each run gets a fresh scratch cwd: programs that create files
            # (bootstraptest does) can't litter the repo or leak state into
            # the determinism double-run / other cases
            try:
                with tempfile.TemporaryDirectory(prefix="difftest-cwd-") as cwd:
                    proc = subprocess.run(
                        [self.ruby, path],
                        capture_output=True,
                        text=True,
                        timeout=self.timeout,
                        cwd=cwd,
                        env={**os.environ, "RUBY_HASH_SEED": "0"},
                    )
            except subprocess.TimeoutExpired:
                return Observation(stdout="", result_repr=None, exception=None, timed_out=True)
            if SENTINEL not in proc.stdout:
                raise HarnessError(
                    f"wrapper produced no observation (exit {proc.returncode}); "
                    f"stderr: {proc.stderr.strip()[:500]}"
                )
            payload = proc.stdout.rsplit(SENTINEL, 1)[1]
            try:
                d = json.loads(payload)
            except json.JSONDecodeError as e:
                raise HarnessError(f"unparseable observation payload: {e}") from e
            exc = d.get("exception")
            return _scrub_program_path(
                Observation(
                    stdout=d["stdout"],
                    result_repr=d.get("result_repr"),
                    exception=(exc[0], exc[1]) if exc else None,
                ),
                path,
            )
        finally:
            os.unlink(path)

    def run_deterministic(self, source: str) -> tuple[Observation | None, str | None]:
        """Run twice; return (observation, None) if both normalized runs agree,
        else (None, reason). Nondeterministic programs are excluded with a reason,
        never silently."""
        a = self.run(source)
        if a.timed_out:
            return None, "timeout"
        # A stack overflow is CRuby's resource-limited approximation of a
        # non-terminating (unbounded-recursion) program: the language semantics
        # say "recurses forever," so there is no well-defined final observation.
        # The stdout printed *before* the overflow depends on the C stack size
        # and frames-per-call, so any implementation that adds frames (the
        # desugar roundtrip wraps each call) overflows at a different depth and
        # prints a different prefix. That prefix is not a stable semantic
        # observable, so exclude with a reason rather than report a false
        # disagreement (same class as `timeout` above; termination-by-construction
        # in tier 1 covers loops but not mutual recursion).
        if a.exception and a.exception[0] == "SystemStackError":
            return None, "SystemStackError (non-terminating recursion; pre-overflow stdout is stack-depth-dependent, not a stable observable)"
        b = self.run(source)
        if a.normalized() != b.normalized():
            return None, "nondeterministic (two control runs differ)"
        return a, None
