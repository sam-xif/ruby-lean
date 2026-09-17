"""The Sorbet toolchain: static checker (`srb tc`) and runtime (`sorbet-runtime`).

Sorbet has *two* halves, and the whole point of the Sorbet difftest work is
that they are separate objects of study (`../ruby-lean/AGENTS.md` §Sorbet §A.3/§A.5):

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

from .control import CRubyRunner, ruby_path

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
# The precision transform: sig-stripping (the `⊑` of the gradual guarantee)
# --------------------------------------------------------------------------

_SIG_STRIP_RB = Path(__file__).resolve().parents[1] / "ruby" / "sig_strip.rb"


@dataclass(frozen=True)
class Unstrippable:
    """The program contains Sorbet constructs that are structural, not
    annotations (T::Struct, T::Enum, T.absurd, …), so no less-precise variant
    of *the same program* exists. Gated with a reason, never mangled."""

    reason: str


class SigStripper:
    """Produce the less-precise variant of a Sorbet-annotated program.

    Implemented as a Prism-based source-to-source transform (`ruby/sig_strip.rb`)
    rather than a regex: `sig do … end` blocks, chained `.checked(:never)`, and
    nested assertions all need real parse structure, and the transform must
    splice byte ranges so that everything it does not touch stays identical.
    """

    def __init__(self, ruby: str | None = None, timeout: float = 30.0):
        self.ruby = ruby or ruby_path()
        self.timeout = timeout

    def strip(self, source: str) -> str | Unstrippable:
        proc = subprocess.run(
            [self.ruby, str(_SIG_STRIP_RB)],
            input=source,
            capture_output=True,
            text=True,
            timeout=self.timeout,
        )
        if proc.returncode == 3:
            return Unstrippable(proc.stderr.strip())
        if proc.returncode != 0:
            raise SorbetUnavailable(
                f"sig_strip failed (exit {proc.returncode}): {proc.stderr.strip()[:300]}"
            )
        return proc.stdout


# Neutralize sorbet-runtime's enforcement without touching the program:
# `call_validation_error_handler` covers sig parameter/return/block checks and
# `inline_type_error_handler` covers the T.let/T.cast/T.must/T.assert_type!
# family (two knobs, because they are two mechanisms). Both are public
# configuration, so this is Sorbet's own supported "checks off" mode rather
# than monkey-patching.
#
# Kept to a SINGLE LINE on purpose: prepending it shifts the program's line
# numbers by exactly one, which keeps any line number that leaks into an
# observation easy to reason about.
_UNCHECKED_PRELUDE = (
    'require "sorbet-runtime"; '
    "T::Configuration.call_validation_error_handler = ->(*) {}; "
    "T::Configuration.inline_type_error_handler = ->(*) {}\n"
)


def unchecked_variant(source: str) -> str:
    """The annotated program with sorbet-runtime enforcement neutralized.

    The third leg of the gradual-guarantee probe: comparing it against the
    stripped variant *attributes* any precise-vs-stripped difference to runtime
    enforcement, which is the only difference the guarantee licenses. Note this
    is deliberately NOT the same as the stripped program — the annotations are
    all still there, still evaluated, still wrapping methods; only their
    failure behavior is silenced.
    """
    return _UNCHECKED_PRELUDE + source


# --------------------------------------------------------------------------
# The Sorbet fragment: what a soundness theorem could be about
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class FragmentResult:
    """`rubycore --fragment`: is this program in the provable subset, and if
    not, why (`ruby-lean/RubyCore/Types/Fragment.lean`)."""

    in_fragment: bool
    violations: tuple[dict, ...]

    def to_json(self) -> dict:
        return {"in_fragment": self.in_fragment, "violations": list(self.violations)}


class FragmentChecker:
    """Ask the Lean model whether a program is in the Sorbet fragment.

    A *static* query: the binary decodes and scans, it does not run anything, so
    the answer is independent of model coverage. Deliberately the same binary
    that carries the semantics — the fragment is the hypothesis of a theorem
    about that semantics, so it must not drift into a separate reimplementation.
    """

    def __init__(self, harness_lib: Path | None = None, lean_bin: Path | None = None,
                 runner: CRubyRunner | None = None):
        root = Path(__file__).resolve().parents[2]
        self.harness_lib = Path(harness_lib) if harness_lib else root / "desugar-dt" / "lib"
        self.lean_bin = Path(lean_bin) if lean_bin else root / "ruby-lean" / ".lake" / "build" / "bin" / "rubycore"
        self.runner = runner or CRubyRunner()

    def check(self, source: str) -> FragmentResult | None:
        """None when the program cannot be desugared or decoded — "we cannot
        say", never a silent False (which would read as "out of fragment")."""
        import json as _json

        proc = subprocess.run(
            [self.runner.ruby, "-e", _EXPORT_SNIPPET_FOR_FRAGMENT, str(self.harness_lib)],
            input=source, capture_output=True, text=True, timeout=self.runner.timeout,
        )
        if proc.returncode != 0:
            return None
        lean = subprocess.run(
            [str(self.lean_bin), "--fragment"],
            input=proc.stdout, capture_output=True, text=True, timeout=self.runner.timeout,
        )
        if lean.returncode != 0:
            return None
        try:
            d = _json.loads(lean.stdout)
        except ValueError:
            return None
        return FragmentResult(bool(d["in_fragment"]), tuple(d.get("violations", [])))


# --------------------------------------------------------------------------
# The static checker: what `check` says
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class CheckResultLean:
    """`rubycore --check`: the static checker's answer
    (`ruby-lean/RubyCore/Types/Core.lean`).

    Two readings, and the distinction is D12's:

    * `decision` — **total**, `accept` or `reject`, never `unknown`. This is what
      `PLAN.md` §1 criterion 2 is stated over. `accept` is licensed by
      `Proof/Static.decision_sound_withPrelude`; `reject` says *the checker did
      not certify this program* and carries no claim about the program at all.
    * `verdict`/`basis` — the **epistemic** reading, unchanged in meaning and in
      value from before D12: `refuted` is *our rules refute this* (the only cell
      the `srb` comparison's pinned zero is about) and `uncertified` is *the
      fragment escaped*. Consumers that compare against `srb`, and the tier-4
      corpus's declared verdicts, read this one — collapsing the two would retire
      that comparison silently.
    """

    verdict: str  # accept | reject | unknown  — the epistemic reading
    inferred_type: str | None
    decision: str | None = None  # accept | reject  — D12's total reading
    basis: str | None = None  # certified | refuted | uncertified

    def to_json(self) -> dict:
        return {"verdict": self.verdict, "type": self.inferred_type,
                "decision": self.decision, "basis": self.basis}


class StaticChecker:
    """Ask the Lean model for the static checker's verdict.

    Same shape and same rationale as `FragmentChecker`: a static query against
    the binary that carries the semantics, so the checker cannot drift into a
    separate reimplementation of itself.
    """

    def __init__(self, harness_lib: Path | None = None, lean_bin: Path | None = None,
                 runner: CRubyRunner | None = None):
        root = Path(__file__).resolve().parents[2]
        self.harness_lib = Path(harness_lib) if harness_lib else root / "desugar-dt" / "lib"
        self.lean_bin = Path(lean_bin) if lean_bin else root / "ruby-lean" / ".lake" / "build" / "bin" / "rubycore"
        self.runner = runner or CRubyRunner()

    def check(self, source: str) -> CheckResultLean | None:
        """None when the program cannot be desugared or decoded — "we cannot
        say". Deliberately distinct from `unknown`, which is the checker having
        looked and abstained; conflating them would let pipeline breakage read
        as honest abstention and quietly flatter the ratchet."""
        import json as _json

        proc = subprocess.run(
            [self.runner.ruby, "-e", _EXPORT_SNIPPET_FOR_FRAGMENT, str(self.harness_lib)],
            input=source, capture_output=True, text=True, timeout=self.runner.timeout,
        )
        if proc.returncode != 0:
            return None
        lean = subprocess.run(
            [str(self.lean_bin), "--check"],
            input=proc.stdout, capture_output=True, text=True, timeout=self.runner.timeout,
        )
        if lean.returncode != 0:
            return None
        try:
            d = _json.loads(lean.stdout)
        except ValueError:
            return None
        return CheckResultLean(str(d["verdict"]), d.get("type"),
                               d.get("decision"), d.get("basis"))


class SigReader:
    """Ask the Lean model which Sorbet signatures a program *declares*
    (`rubycore --sigs`, `ruby-lean/RubyCore/Types/SigRead.lean`).

    Static, like `FragmentChecker` and `StaticChecker`, and against the same
    binary — the reader is what a later typing layer will consume, so it must not
    drift into a separate reimplementation.
    """

    def __init__(self, harness_lib: Path | None = None, lean_bin: Path | None = None,
                 runner: CRubyRunner | None = None):
        root = Path(__file__).resolve().parents[2]
        self.harness_lib = Path(harness_lib) if harness_lib else root / "desugar-dt" / "lib"
        self.lean_bin = Path(lean_bin) if lean_bin else root / "ruby-lean" / ".lake" / "build" / "bin" / "rubycore"
        self.runner = runner or CRubyRunner()

    def read(self, source: str) -> list[dict] | None:
        """`[{method, params: [{name, type}], returns}]`, or None when the
        program could not be desugared or decoded."""
        import json as _json

        proc = subprocess.run(
            [self.runner.ruby, "-e", _EXPORT_SNIPPET_FOR_FRAGMENT, str(self.harness_lib)],
            input=source, capture_output=True, text=True, timeout=self.runner.timeout,
        )
        if proc.returncode != 0:
            return None
        lean = subprocess.run(
            [str(self.lean_bin), "--sigs"],
            input=proc.stdout, capture_output=True, text=True, timeout=self.runner.timeout,
        )
        if lean.returncode != 0:
            return None
        try:
            return _json.loads(lean.stdout)["sigs"]
        except (ValueError, KeyError):
            return None


# Same desugar-and-export snippet the Lean SUT uses; duplicated as a module-level
# constant here to avoid importing `sut` (which imports `compare`, which imports
# this module).
_EXPORT_SNIPPET_FOR_FRAGMENT = """\
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
# the `raised != stuck` point of `../ruby-lean/AGENTS.md` §Type safety as reachability §2). Classifying
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
