"""The Sorbet toolchain: static checker (`srb tc`) and runtime (`sorbet-runtime`).

Sorbet has *two* halves, and the whole point of the Sorbet difftest work is
that they are separate objects of study (`../docs/semantics/types-and-preservation.md`
§A.3/§A.5):

- **static** — `srb tc` accepts or rejects a program. Sorbet is unsound by
  design, so acceptance is *not* a safety claim; this module exposes it as an
  **oracle** we compare against, never as a source of truth.
- **runtime** — `sorbet-runtime` wraps every `sig`-annotated method in a
  checking wrapper that raises `TypeError` on a violation. That raise is the
  "blame" outcome of the gradual-safety theorem, and it is `obs`-visible, hence
  differential-testable with the machinery this engine already has.

Neither tool is vendored: both are gems, resolved at run time with an explicit
recipe when missing (same discipline as `sources.HARVEST_RECIPE`).
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

from .control import ruby_path

SETUP_RECIPE = """\
The Sorbet toolchain is not vendored. To install it:
  gem install sorbet sorbet-runtime
`srb` lands in `$(gem environment gemdir)/bin`, which is not always on PATH;
override the resolved path with DIFFTEST_SRB=/path/to/srb."""


class SorbetUnavailable(RuntimeError):
    """The Sorbet toolchain is missing (never silently degraded to a verdict)."""


@lru_cache(maxsize=1)
def _gem_bin_dir() -> Path | None:
    try:
        out = subprocess.run(
            ["gem", "environment", "gemdir"], capture_output=True, text=True, check=True
        ).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None
    d = Path(out) / "bin"
    return d if d.is_dir() else None


@lru_cache(maxsize=1)
def srb_path() -> str | None:
    """Resolve the `srb` static checker. DIFFTEST_SRB overrides; then PATH; then
    the gem executable directory (Homebrew Ruby does not put it on PATH)."""
    env = os.environ.get("DIFFTEST_SRB")
    if env:
        return env
    found = shutil.which("srb")
    if found:
        return found
    gem_bin = _gem_bin_dir()
    if gem_bin and (gem_bin / "srb").exists():
        return str(gem_bin / "srb")
    return None


@lru_cache(maxsize=1)
def sorbet_runtime_available() -> bool:
    """True iff `require "sorbet-runtime"` succeeds under the pinned CRuby."""
    proc = subprocess.run(
        [ruby_path(), "-e", 'require "sorbet-runtime"'],
        capture_output=True,
        text=True,
        timeout=60.0,
    )
    return proc.returncode == 0


def require_toolchain(static: bool = True, runtime: bool = True) -> None:
    """Raise SorbetUnavailable (with the recipe) unless the requested halves exist."""
    missing = []
    if static and srb_path() is None:
        missing.append("srb (gem `sorbet`)")
    if runtime and not sorbet_runtime_available():
        missing.append("sorbet-runtime (gem `sorbet-runtime`)")
    if missing:
        raise SorbetUnavailable(f"missing: {', '.join(missing)}\n{SETUP_RECIPE}")


# --------------------------------------------------------------------------
# Static half: `srb tc`
# --------------------------------------------------------------------------

# `file:LINE: message https://srb.help/CODE` — the URL suffix carries the error
# code. Sorbet emits no machine-readable error format for `tc` (only
# --metrics-file counters and the LSP protocol), so the human output is parsed;
# the trailing srb.help URL makes the code extraction unambiguous. Continuation
# lines (context, snippets) are indented and deliberately skipped.
_ERR_RE = re.compile(r"^(?P<file>\S+?):(?P<line>\d+): (?P<msg>.*?) https://srb\.help/(?P<code>\d+)\s*$")
_ERR_NOCODE_RE = re.compile(r"^(?P<file>\S+?):(?P<line>\d+): (?P<msg>.*?)\s*$")
_COUNT_RE = re.compile(r"^Errors: (\d+)\s*$")


@dataclass(frozen=True)
class StaticError:
    line: int
    code: int | None  # the srb.help error code, when the line carries one
    message: str

    def to_json(self) -> dict:
        return {"line": self.line, "code": self.code, "message": self.message}


@dataclass(frozen=True)
class StaticResult:
    """What `srb tc` said about one program."""

    errors: tuple[StaticError, ...]
    raw: str

    @property
    def ok(self) -> bool:
        return not self.errors

    def to_json(self) -> dict:
        return {"ok": self.ok, "errors": [e.to_json() for e in self.errors]}


class SorbetStatic:
    """Run `srb tc` on a single standalone program.

    `--no-config` keeps each check hermetic (no `sorbet/config`, no RBI
    payload from a surrounding project): the program plus Sorbet's built-in
    RBIs for `T`, nothing else. That is the right scope for corpus programs,
    which are self-contained by construction.
    """

    def __init__(self, srb: str | None = None, timeout: float = 60.0):
        self.srb = srb or srb_path()
        self.timeout = timeout

    def check(self, source: str, force_sigil: str | None = None) -> StaticResult:
        if self.srb is None:
            raise SorbetUnavailable(f"srb not found\n{SETUP_RECIPE}")
        with tempfile.TemporaryDirectory(prefix="difftest-srb-") as d:
            path = Path(d) / "case.rb"
            path.write_text(source)
            cmd = [self.srb, "tc", "--no-config", "--color=never"]
            if force_sigil:
                cmd += ["--typed", force_sigil]
            cmd.append(str(path))
            proc = subprocess.run(
                cmd, capture_output=True, text=True, timeout=self.timeout, cwd=d
            )
            raw = (proc.stdout + proc.stderr).replace(str(path), "case.rb")
        errors = tuple(_parse_errors(raw))
        # `srb tc` exits 0 when clean and 100 when it found type errors; other
        # nonzero exits mean the tool itself failed. Rather than pin the exact
        # code (it has drifted across releases), accept any exit that came with
        # parsed errors and treat a nonzero exit with *no* parsed errors as a
        # tool failure — that way a future code change degrades loudly, never
        # into a silent "clean".
        if proc.returncode != 0 and not errors:
            raise SorbetUnavailable(
                f"srb tc failed (exit {proc.returncode}): {raw.strip()[:500]}"
            )
        return StaticResult(errors=errors, raw=raw)


def _parse_errors(raw: str) -> list[StaticError]:
    errors: list[StaticError] = []
    for line in raw.splitlines():
        if not line or line[0].isspace():
            continue  # continuation/context line
        m = _ERR_RE.match(line)
        if m:
            errors.append(
                StaticError(int(m["line"]), int(m["code"]), m["msg"].strip())
            )
            continue
        m = _ERR_NOCODE_RE.match(line)
        if m and not _COUNT_RE.match(line):
            errors.append(StaticError(int(m["line"]), None, m["msg"].strip()))
    return errors


# --------------------------------------------------------------------------
# Runtime half: classifying a sorbet-runtime sig violation
# --------------------------------------------------------------------------

# sorbet-runtime's default handlers raise a plain ::TypeError, which is
# indistinguishable *by class* from a genuine Ruby TypeError (`1 + "a"`). The
# gradual-guarantee relation (N29) needs to tell them apart, so we classify by
# message shape. These are the message prefixes emitted by
# T::Private::Methods::CallValidation (parameter/return/bind) and by the
# T.let/T.cast/T.must/T.assert_type! assertion family.
#
# Considered and rejected: installing a custom
# `T::Configuration.call_validation_error_handler` that raises a distinguishable
# class. It is more robust, but it *changes the program's semantics* — a program
# under test may itself `rescue TypeError`, and the corpus deliberately contains
# such programs (a locally-rescued sig violation is a type-safe program, exactly
# the `raised != stuck` point of type-safety-by-reachability.md §2). Classifying
# after the fact leaves the observed behavior untouched.
_SIG_ERROR_PATTERNS = (
    "Parameter '",            # CallValidation: argument type check
    "Return value:",          # CallValidation: return type check
    "Block parameter",        # CallValidation: block arg check
    "T.let:",
    "T.cast:",
    "T.must:",
    "T.bind:",
    "T.assert_type!:",
    "Expected type ",         # the shared tail of the CallValidation messages
    "Passed `nil` into T.must",
)


def is_sorbet_runtime_error(exception: tuple[str, str] | None) -> bool:
    """True iff this observed exception is a sorbet-runtime enforcement failure
    (the "blame" outcome), as opposed to a Ruby-level error of the same class."""
    if not exception:
        return False
    cls, msg = exception
    if cls not in ("TypeError", "TypeError::TypeError"):
        return False
    return any(p in msg for p in _SIG_ERROR_PATTERNS)
