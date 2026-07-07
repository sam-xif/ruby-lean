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
            return Observation(
                stdout=d["stdout"],
                result_repr=d.get("result_repr"),
                exception=(exc[0], exc[1]) if exc else None,
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
        b = self.run(source)
        if a.normalized() != b.normalized():
            return None, "nondeterministic (two control runs differ)"
        return a, None
