#!/usr/bin/env python3
"""Compose the ratchet's Homebrew-slice rungs (tiers 18 and 19) into
`../slice/*.rb` — one **self-contained, runnable** Ruby program per rung.

Why this is a separate script from `generate_corpus.py`. Every other rung in the
corpus is a Ruby string written inline in the generator; these eight-plus are
*Homebrew's own source*, which lives in `ruby/homebrew/vendor/brew` — a
gitignored vendored checkout that nobody can assume is present. So the
composition is done **once**, here, and its output (`../slice/*.rb`) is
committed. `generate_corpus.py` then reads those files like any other rung
source and never needs the vendor tree; only *re-composing* does.

A composed program is three parts, in the same order and from the same places as
`homebrew/slice-driver/build.py` (which composes the whole-slice program the same
way — see its docstring for why the boot stubs are imported rather than copied):

1. **boot stubs** — `difftest/tiers/tier0/rspec_harvest.py`, verbatim.
2. **the library** — `linker` over the rung's entry file(s), splicing its
   require-closure into one program.
3. **the driver** — `../slice/drivers/<name>.rb`, a main that exercises the
   file's own API. Real calls only: nothing is reimplemented here, and no value
   is printed that the slice would not compute.

    python3 scripts/build_slice_rungs.py --brew ../homebrew/vendor/brew

Then `python3 scripts/generate_corpus.py` to re-derive the corpus JSON, and
`scripts/run_ratchet.sh` to check the ladder (which difftests every composed
program against CRuby first — these are ordinary rungs in that respect).
"""

from __future__ import annotations

import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RATCHET_DIR = os.path.normpath(os.path.join(HERE, ".."))
RUBY_ROOT = os.path.normpath(os.path.join(RATCHET_DIR, ".."))
SLICE_DIR = os.path.join(RATCHET_DIR, "slice")
DRIVER_DIR = os.path.join(SLICE_DIR, "drivers")

# (rung name, entry files in load order). Each entry is resolved against
# `Library/Homebrew`; the linker pulls in its require-closure, so the file count
# per rung is larger than the entry count (e.g. `pkg_version.rb` is 3 files).
#
# Tier 18 — one rung per slice file, in dependency order: a file's rung links
# only what that file needs, so the ladder climbs the slice file by file rather
# than facing all eight at once.
PER_FILE = [
    ("semver",        ["vulns/semver.rb"]),
    ("cvss",          ["vulns/cvss.rb"]),
    ("purl",          ["vulns/purl.rb"]),
    ("version-parser", ["version/parser.rb"]),
    ("version",       ["version.rb"]),
    ("pkg-version",   ["pkg_version.rb"]),
    ("identify",      ["vulns/identify.rb"]),
    # `vulns/vulnerability.rb` `require`s only cvss and semver, but its
    # `ECOSYSTEM` comparator and its `:fixed` tiebreak both name `Version`,
    # which Homebrew's boot path supplies and a require-closure does not. That
    # is the "undefined constants" coupling `homebrew/closure.py` measures; the
    # rung links `version.rb` alongside so the file's own branches are all
    # reachable rather than half of them dying on a `NameError`.
    ("vulnerability", ["version.rb", "vulns/vulnerability.rb"]),
]

# Tier 19 — the whole slice, linked from the three entry points that reach all
# eight files (the same three `homebrew/slice-driver/build.py` uses).
WHOLE_ENTRIES = ["pkg_version.rb", "vulns/vulnerability.rb", "vulns/identify.rb"]
WHOLE = [
    ("slice-whole", WHOLE_ENTRIES),
    ("slice-input-sweep", WHOLE_ENTRIES),
    ("slice-adversarial", WHOLE_ENTRIES),
]

# Drivers that already exist elsewhere in the tree are **referenced**, not copied:
# a second copy of the demonstration is a second thing to drift, and these three
# are the artifacts `homebrew/slice-driver/` already runs and documents.
DRIVER_OVERRIDE = {
    "slice-whole": os.path.join(RUBY_ROOT, "homebrew", "slice-driver", "driver.rb"),
}


# `extend/blank.rb`'s per-class rows, verbatim from
# `Library/Homebrew/extend/blank/{nil_class,false_class}.rb`.
#
# **Why the ratchet adds these and `homebrew/slice-driver/build.py` does not.**
# The shared harness stub (`rspec_harvest.BLANK_STUB`) is `Object#blank?` alone:
# `respond_to?(:empty?) ? !!empty? : false`. That is upstream's `Object` row and
# it happens to be right for Array/Hash/String/Symbol, whose `blank?` upstream
# *is* `empty?` — but it is **wrong for `nil`**, which upstream declares blank
# and the stub reports as *present*, because `NilClass` has no `empty?`.
#
# It stays silent almost everywhere and is fatal in exactly one slice file:
# `version/parser.rb` guards with `return if match.blank?` and
# `return @block.call(version) if @block.present?`, so with the `Object` row
# alone a non-matching regex reaches `nil.captures` and an absent block reaches
# `nil.call`. `RegexParser#parse` is unusable without this, in both executors
# alike — which is why it went unnoticed: the harvested corpus difftests
# *agreement*, and both sides were wrong together.
#
# Added here rather than in the shared harness so the harvested corpus's
# programs do not change underneath it; the two stub sets differing is recorded
# in `../AGENTS.md`.
BLANK_NIL_STUB = """
class NilClass
  sig { returns(TrueClass) }
  def blank? = true

  sig { returns(FalseClass) }
  def present? = false
end

class FalseClass
  sig { returns(TrueClass) }
  def blank? = true

  sig { returns(FalseClass) }
  def present? = false
end
"""


def _imports():
    for p in (RUBY_ROOT, os.path.join(RUBY_ROOT, "difftest")):
        if p not in sys.path:
            sys.path.insert(0, p)
    from difftest.tiers.tier0 import rspec_harvest as harvest  # noqa: E402
    from linker import emit, graph                             # noqa: E402
    from linker.cli import SCRIPT, default_ruby                # noqa: E402

    return harvest, emit, graph, SCRIPT, default_ruby


def compose(brew_root: str, name: str, entry_names: list[str]) -> str:
    harvest, emit, graph, script, default_ruby = _imports()
    lib = os.path.join(brew_root, "Library", "Homebrew")
    entries = [os.path.join(lib, f) for f in entry_names]
    missing = [e for e in entries if not os.path.isfile(e)]
    if missing:
        # /tmp gets reaped and the tools downstream fail *quietly*; fail loudly.
        raise SystemExit(f"missing slice files under {lib}: {', '.join(missing)}")

    nodes = graph.build(entries, [lib], default_ruby(), script)
    linked = emit.link(nodes, entries, lib, {"platform": "generic"})

    boot = (
        harvest.SORBET_REQUIRE
        # `pkg_version.rb` does `extend Forwardable`. Emitted unconditionally so
        # every rung's boot prefix is byte-identical: the prefix is *harness*,
        # and a prefix that varies per rung is a second thing to keep in sync.
        + 'require "forwardable"\n'
        + harvest.BLANK_STUB
        + BLANK_NIL_STUB
        + harvest.PATHNAME_STEM_STUB
        + harvest.OUTPUT_STUB
    )
    driver_path = DRIVER_OVERRIDE.get(name, os.path.join(DRIVER_DIR, f"{name}.rb"))
    driver = open(driver_path).read()
    m = linked.manifest
    header = (
        "# Generated by ratchet/scripts/build_slice_rungs.py — do not edit, regenerate.\n"
        "# boot stubs: difftest/tiers/tier0/rspec_harvest.py (SORBET_REQUIRE, BLANK_STUB,\n"
        '#             PATHNAME_STEM_STUB, OUTPUT_STUB) + require "forwardable"\n'
        "#             + BLANK_NIL_STUB (extend/blank/{nil_class,false_class}.rb)\n"
        f"# library:    {len(m['files'])} file(s) linked from {', '.join(entry_names)};"
        f" {len(m['external_requires'])} external, {len(m['cycles'])} cycles\n"
        f"# driver:     {os.path.relpath(driver_path, RUBY_ROOT)}\n"
    )
    return header + boot + linked.source + "\n" + driver


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--brew", default=os.path.join(RUBY_ROOT, "homebrew", "vendor", "brew"),
                    help="a Homebrew/brew checkout (default: the vendored one)")
    ap.add_argument("--only", default=None, help="compose just this rung name")
    a = ap.parse_args()

    os.makedirs(SLICE_DIR, exist_ok=True)
    for name, entries in PER_FILE + WHOLE:
        if a.only and a.only != name:
            continue
        src = compose(a.brew, name, entries)
        out = os.path.join(SLICE_DIR, f"{name}.rb")
        with open(out, "w") as f:
            f.write(src)
        print(f"wrote slice/{name}.rb ({len(src.splitlines())} lines)")


if __name__ == "__main__":
    main()
