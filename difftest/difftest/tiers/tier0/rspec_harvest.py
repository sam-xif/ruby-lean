"""Harvest Homebrew's RSpec examples for the slice into tier-0 programs (W4a).

Three stages, each owned by the tool that is already good at it:

1. **`linker`** builds the library prefix. A spec file says `require "version"`;
   the linker turns that into one self-contained program (workstream W3), which
   is exactly the preamble an example needs.
2. **`difftest/ruby/rspec_harvest.rb`** parses the spec with Prism and rewrites
   every `expect(...).to matcher` into a call to one of two runtime helpers.
   Ruby parses Ruby (the same division of labour as the linker, LK1).
3. This module assembles `prefix + preamble + body` into one program per
   example, writes a manifest, and — the part the plan insists on — writes a
   **skip report**, so nothing is silently dropped.

The corpus is generated, not vendored: it embeds ~20 KB of upstream Homebrew per
example. Same treatment as `bootstraptest` (harvested on demand, gitignored).

    python3 -m difftest harvest-rspec --brew /path/to/brew
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass

# Files linked from Homebrew's boot path (it loads them globally; the emitted
# program has no boot path). Empty today — see BLANK_STUB for why `extend/blank`
# is not among them.
BOOT_FEATURES: list[str] = []

# `vulns/vulnerability.rb` does `include Utils::Output::Mixin` — the one
# external constant the slice touches (homebrew/PLAN.md §2). Neither linking nor
# including `utils/output.rb` verbatim works: every `require` in it is inside a
# method body (so linking follows them into the 227-file cycle the slice exists
# to avoid), and its last three lines are `extend Mixin` / `$stdout.extend
# Mixin` / `$stderr.extend Mixin`, which reach IO objects the model does not
# have.
#
# So the corpus supplies the module itself. The slice reaches **exactly one** of
# its 25 methods — `odebug`, from one rescue path in `in_interval_permissive?` —
# and `odebug` is *observationally equivalent to a no-op here*: it returns early
# unless debug is on (it is not, since nothing sets `Context.current.debug?`),
# and even when it does fire it writes to **stderr**, which the observation
# function does not capture. So this stand-in cannot change any comparison,
# and both executors run it.
OUTPUT_STUB = """
module Utils
  module Output
    module Mixin
      # See difftest/implementation-notes.md N36: upstream `odebug` returns
      # early unless debug is enabled and otherwise writes to stderr, neither of
      # which is observable here.
      # The sig is upstream's, verbatim (`utils/output.rb:32`) — see N48: a stub
      # without one is a `missing-sig` row in `--fragment` for a method that *is*
      # annotated upstream, i.e. our bug rather than the slice's.
      sig { params(title: T.any(String, Exception), sput: T.anything, always_display: T::Boolean).void }
      def odebug(title, *sput, always_display: false)
        nil
      end
    end
  end
end
"""

# The eight spec files of the version + vulnerability slice, paired with the
# library feature each one requires (homebrew/PLAN.md §2).
SLICE = [
    ("version_spec.rb", "version"),
    ("version/parser_spec.rb", "version/parser"),
    ("pkg_version_spec.rb", "pkg_version"),
    ("vulns/semver_spec.rb", "vulns/semver"),
    ("vulns/cvss_spec.rb", "vulns/cvss"),
    ("vulns/purl_spec.rb", "vulns/purl"),
    ("vulns/vulnerability_spec.rb", "vulns/vulnerability"),
    ("vulns/identify_spec.rb", "vulns/identify"),
]

# The two runtime helpers every emitted program carries. They print *both* the
# actual value and the matcher's verdict: tier 0 asks whether CRuby and the
# model agree, not whether Homebrew's suite passes, so a model bug that changes
# a value shows up even where the verdict would agree either way.
PREAMBLE = '''
def __exp(label, act, vd)
  ok = true
  v = begin
    act.call
  rescue StandardError => e
    ok = false
    "#{e.class}: #{e.message}"
  end
  if ok
    w = begin
      vd.call(v) ? true : false
    rescue StandardError => e
      "#{e.class}: #{e.message}"
    end
    puts("#{label} #{v.inspect} #{w.inspect}")
  else
    puts("#{label} raised #{v}")
  end
end

def __exr(label, blk, cls, negated)
  begin
    blk.call
    puts("#{label} no-raise #{negated}")
  rescue StandardError => e
    m = cls.nil? ? "any" : (e.is_a?(cls) ? "match" : "nomatch")
    puts("#{label} raised #{e.class} #{m} #{negated}")
  end
end
'''


@dataclass
class Example:
    file: str
    line: int
    name: str
    described: str | None
    memos: list
    helpers: list
    body: str
    skip: str | None

    @property
    def ident(self) -> str:
        stem = self.file.replace("/", "-").replace("_spec.rb", "")
        return f"{stem}-{self.line:04d}"


def _repo_root() -> str:
    """`ruby/` — the directory that holds both `difftest/` and `linker/`."""
    here = os.path.dirname(os.path.abspath(__file__))
    return os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(here))))


def _import_linker():
    root = _repo_root()
    if root not in sys.path:
        sys.path.insert(0, root)
    from linker import emit, graph  # noqa: E402
    from linker.cli import SCRIPT, default_ruby  # noqa: E402

    return emit, graph, SCRIPT, default_ruby


def _ruby() -> str:
    return _import_linker()[3]()


def harvest_file(spec_path: str, ruby: str, script: str) -> list[Example]:
    proc = subprocess.run([ruby, script, spec_path], capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"{spec_path}: {proc.stderr.strip()[:400]}")
    out = []
    for line in proc.stdout.splitlines():
        r = json.loads(line)
        out.append(
            Example(file=r["file"], line=r["line"], name=r["name"],
                    described=r["described"], memos=r["memos"],
                    helpers=r["helpers"], body=r["body"], skip=r["skip"])
        )
    return out


# The slice's files use `T::Sig`/`T::Helpers` but never require sorbet-runtime
# themselves — Homebrew loads it once from its boot path. The emitted program
# has no boot path, so it requires it explicitly. CRuby then loads the real gem;
# the model's `require` is a no-op and its `T` comes from the prelude shim (L80),
# which is the arrangement the tier-4 Sorbet corpus already uses.
# `class Module; include T::Sig; end` is Homebrew's own boot line
# (`extend/module.rb:5`); without it `sig` is not a method in a class body and
# the slice's files do not extend `T::Sig` themselves.
# `version.rb` calls `String#blank?`, which Homebrew gets from `extend/blank.rb`.
# That file is *not* linked in: it pulls in ten per-class specializations, and
# the String one alone needs a POSIX bracket class, `Encoding` and
# `Regexp::FIXEDENCODING` — none of which the slice uses and none of which the
# model covers, so linking it would gate every program on infrastructure the
# slice does not exercise. Instead both executors run this stand-in, copied from
# `extend/blank.rb`'s own `Object#blank?` (minus the `T.unsafe`, which is
# identity at runtime). It is the **only** place the corpus substitutes for
# upstream code, and it is boot-path code rather than slice code.
# The three sigs are upstream's, verbatim (`extend/blank.rb:20,26,46`) — N48.
BLANK_STUB = """
class Object
  sig { returns(T::Boolean) }
  def blank?
    respond_to?(:empty?) ? !!empty? : false
  end

  sig { returns(T::Boolean) }
  def present? = !blank?

  sig { returns(T.nilable(T.self_type)) }
  def presence = present? ? self : nil
end
"""

SORBET_REQUIRE = (
    'require "sorbet-runtime"\n'
    'class Module\n  include T::Sig\nend\n'
    # `Version.detect` wraps its argument in `Pathname(...)` and `Version.parse`
    # percent-decodes with `URI`. Homebrew loads both from its boot path; the
    # control has no boot path, so the program requires them and the model
    # recognises both (the pure halves are in its prelude, L112).
    'require "pathname"\nrequire "uri"\n'
)

# `Pathname#stem` is **Homebrew's**, not Ruby's (`extend/pathname.rb:187`), so it
# cannot live in the model's prelude: that would make the model answer something
# the control cannot. Copied verbatim, like BLANK_STUB, so both executors run the
# same code. `extend/pathname.rb` itself is 523 lines of filesystem work and the
# slice reaches exactly this one method of it.
PATHNAME_STEM_STUB = """
class Pathname
  sig { returns(String) }
  def stem
    File.basename(self, extname)
  end
end
"""

# Stdlib the slice's *library* code reaches but never requires, because Homebrew
# loads it from its boot path. The control has it (RSpec and sorbet-runtime pull
# most of it in transitively); the model does not. Emitting the `require`
# explicitly, and only for the programs whose library actually mentions the
# constant, turns each into an honest refusal (L109: `require` of an unmodeled
# library gates) instead of a `NameError` the control never sees — and keeps the
# gate confined to the programs that need it. `URI` is the expensive one: it is
# what `Version.detect` parses URLs with, so it covers the `be_detected_from`
# family.
# Only the constants the model would *not* already gate on: `Pathname` and
# `Set` are in its CRuby name table, so an unmodeled reference to them is
# already an honest Unsupported and needs no help.
STDLIB_REQUIRES = [("Forwardable", "forwardable")]

# The same problem one level down: `to_json` is a *method* the json library adds
# to every object, so an unmodeled reference is a NoMethodError rather than a
# missing constant, and the constant gate cannot catch it. Scanned over the
# **example** only, not the library: `version.rb` defines its own `to_json` and
# scanning the prefix too would gate 28 programs that never call one.
STDLIB_METHOD_REQUIRES = [("to_json", "json")]



DESCRIBED_RE = re.compile(r"(^|[^\w.:])described_class\b")


def _sub_described(text: str) -> str:
    """`described_class` is an RSpec method; the emitted program binds it as a
    constant instead. The rewriter does this for example bodies; memo and helper
    bodies are carried through as source text, so they need it too."""
    return DESCRIBED_RE.sub(lambda m: m.group(1) + "DESCRIBED_CLASS", text)


def program(ex: Example, prefix: str) -> str:
    """`library + helpers + memos + body`, as one self-contained program."""
    parts = [SORBET_REQUIRE]
    for const, feature in STDLIB_REQUIRES:
        if re.search(r"\b" + const + r"\b", prefix):
            parts.append(f'require "{feature}"\n')
    parts += [BLANK_STUB, PATHNAME_STEM_STUB, prefix, PREAMBLE]
    if ex.described:
        parts.append(f"DESCRIBED_CLASS = {ex.described}\n")
    for m in ex.memos:
        if not m["name"]:
            continue
        # `let` is memoized per example, and an example runs once, so an ivar
        # cache on main reproduces it exactly.
        parts.append(
            f"def {m['name']}\n"
            f"  @__{m['name']} = ({_sub_described(m['body'])}) unless "
            f"defined?(@__{m['name']}) && "
            f"!@__{m['name']}.nil?\n"
            f"  @__{m['name']}\n"
            f"end\n"
        )
    for h in ex.helpers:
        parts.append(_sub_described(h) + "\n")
    for m in ex.memos:
        if m["name"] and m["bang"]:
            parts.append(f"{m['name']}\n")  # let! runs eagerly
    parts.append(f"# {ex.file}:{ex.line} — {ex.name}\n")
    parts.append(ex.body)
    parts.append("\nnil\n")
    body = "\n".join(parts)
    example_only = ex.body + "".join(m["body"] for m in ex.memos) + "".join(ex.helpers)
    extra = "".join(
        f'require "{feature}"\n'
        for token, feature in STDLIB_METHOD_REQUIRES
        if re.search(r"\b" + token + r"\b", example_only)
    )
    return extra + body


def build_prefix(feature: str, brew_root: str, ruby: str) -> str:
    """Link the library the spec requires into one program (W3)."""
    emit, graph, script, _ = _import_linker()
    lib = os.path.join(brew_root, "Library", "Homebrew")
    entries = [os.path.join(lib, f + ".rb") for f in BOOT_FEATURES + [feature]]
    nodes = graph.build(entries, [lib], ruby, script)
    linked = emit.link(nodes, entries, lib, {"platform": "generic"}).source
    return OUTPUT_STUB + linked


def harvest(brew_root: str, out_dir: str, ruby: str | None = None) -> dict:
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.path.dirname(os.path.dirname(os.path.dirname(here)))  # difftest/
    script = os.path.join(root, "ruby", "rspec_harvest.rb")
    ruby = ruby or _ruby()
    test_dir = os.path.join(brew_root, "Library", "Homebrew", "test")

    os.makedirs(out_dir, exist_ok=True)
    manifest, skipped = [], []
    for spec, feature in SLICE:
        spec_path = os.path.join(test_dir, spec)
        if not os.path.isfile(spec_path):
            skipped.append({"file": spec, "reason": "spec file not found"})
            continue
        prefix = build_prefix(feature, brew_root, ruby)
        for ex in harvest_file(spec_path, ruby, script):
            rel = os.path.relpath(ex.file, test_dir)
            ex.file = rel
            if ex.skip:
                skipped.append({"file": rel, "line": ex.line, "name": ex.name,
                                "reason": ex.skip})
                continue
            path = os.path.join(out_dir, ex.ident + ".rb")
            with open(path, "w", encoding="utf-8") as f:
                f.write(program(ex, prefix))
            # Validation gate: the corpus only holds programs the *control* can
            # actually execute. A program CRuby cannot run would show up as a
            # `control_invalid` verdict forever and teach us nothing, so it is
            # reported as a skip instead. (Two of the slice's examples reach
            # constants outside it — `URI` and `HOMEBREW_CELLAR`.)
            proc = subprocess.run([ruby, path], capture_output=True, text=True)
            if proc.returncode != 0:
                os.unlink(path)
                first = (proc.stderr.strip().splitlines() or [""])[0]
                skipped.append({"file": rel, "line": ex.line, "name": ex.name,
                                "reason": f"control cannot run it: {first[-160:]}"})
                continue
            manifest.append({"id": ex.ident, "file": rel, "line": ex.line,
                             "name": ex.name, "described": ex.described,
                             "feature": feature})

    with open(os.path.join(out_dir, "manifest.json"), "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=1)
        f.write("\n")
    with open(os.path.join(out_dir, "skipped.json"), "w", encoding="utf-8") as f:
        json.dump(skipped, f, indent=1)
        f.write("\n")
    return {"harvested": len(manifest), "skipped": len(skipped), "out": out_dir}
