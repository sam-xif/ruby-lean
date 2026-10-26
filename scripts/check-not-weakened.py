#!/usr/bin/env python3
"""Fail if a change weakens what `make check` checks.

    scripts/check-not-weakened.py                       # the working tree against origin/main
    scripts/check-not-weakened.py --base REF --head REF # one commit against another

`make check` passing says the repository meets its recorded standard. This
says the change did not lower that standard to get there. It compares the two
versions file by file and fails if any of these moved the wrong way:

  recorded results   difftest/coverage-baseline.json, desugar/coverage-baseline.json,
                     books/corpus/accepted.txt, and each unit-test suite's
                     coverage-baseline.json: no number may fall, and no accepted
                     program or measured file may disappear
  the checks         the targets `make check` runs; the theorems whose axioms are
                     audited (`#print axioms`); the theorems the comparator
                     re-checks, and the axioms it permits
  escape hatches     the number of `sorry`, `native_decide`, axiom declarations,
                     lint suppressions, skipped tests and ignored errors
  tests              the number of test functions

It only reads files. In CI it runs from the base branch's copy of itself on a
pull request's merge commit (.github/workflows/not-weakened.yml), so a change
cannot edit the check that judges it, and nothing the change contains is run.

A change that has to weaken one of these (removing a test that tested nothing,
say) needs a maintainer to merge it; the message says what moved.
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Not counted: programs under test, which are not code, and this file, which
# names every pattern it counts.
NOT_CODE = [
    "*/corpus/*",
    "difftest/ruby/mutations/*",
    "ruby-lean/prelude/*",
    "scripts/check-not-weakened.py",
]


class Tree:
    """One version of the repository: a commit, or the working tree when ref is None."""

    def __init__(self, ref: str | None):
        self.ref = ref
        self._cache: dict[str, str | None] = {}
        if ref is None:
            out = git("ls-files", "--cached", "--others", "--exclude-standard")
            self.files = [f for f in out.splitlines() if (ROOT / f).is_file()]
        else:
            self.files = git("ls-tree", "-r", "--name-only", ref).splitlines()
        self._present = set(self.files)

    def name(self) -> str:
        return self.ref or "the working tree"

    def exists(self, path: str) -> bool:
        return path in self._present

    def read(self, path: str) -> str | None:
        if path not in self._cache:
            self.preload([path])
        return self._cache[path]

    def preload(self, paths: list[str]) -> None:
        """Read many files at once (one `git cat-file` for a commit)."""
        todo = [p for p in paths if p not in self._cache]
        for p in todo:
            if p not in self._present:
                self._cache[p] = None
        todo = [p for p in todo if p in self._present]
        if not todo:
            return
        if self.ref is None:
            for p in todo:
                self._cache[p] = (ROOT / p).read_text(errors="replace")
            return
        request = "".join(f"{self.ref}:{p}\n" for p in todo).encode()
        out = subprocess.run(
            ["git", "cat-file", "--batch"], input=request, capture_output=True, cwd=ROOT, check=True
        ).stdout
        pos = 0
        for p in todo:
            header_end = out.index(b"\n", pos)
            size = int(out[pos:header_end].split()[2])
            self._cache[p] = out[header_end + 1 : header_end + 1 + size].decode(errors="replace")
            pos = header_end + 1 + size + 1

    def matching(self, globs: list[str]) -> list[str]:
        return [
            f
            for f in self.files
            if any(fnmatch.fnmatch(f, g) for g in globs)
            and not any(fnmatch.fnmatch(f, g) for g in NOT_CODE)
        ]


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], capture_output=True, text=True, cwd=ROOT, check=True
    ).stdout


@dataclass
class Report:
    failures: list[str] = field(default_factory=list)
    lines: list[str] = field(default_factory=list)

    def ok(self, what: str) -> None:
        self.lines.append(f"  ok    {what}")

    def fail(self, what: str, why: str) -> None:
        self.lines.append(f"  FAIL  {what}: {why}")
        self.failures.append(f"{what}: {why}")


def load_json(tree: Tree, path: str) -> dict | None:
    text = tree.read(path)
    return None if text is None else json.loads(text)


# ── Recorded results ─────────────────────────────────────────────────────────

# file -> {key: direction}; "up" may not fall, "down" may not rise, "same" may not change
NUMBERS = {
    "difftest/coverage-baseline.json": {
        "ran": "same",
        "agree": "up",
        "sut_unsupported": "down",
        "not_compared": "down",
        "disagree": "down",
    },
    "desugar/coverage-baseline.json": {"in_fragment": "up", "parseable": "same"},
}

COVERAGE_BASELINES = [
    "desugar/test/coverage-baseline.json",
    "books/scripts/test/coverage-baseline.json",
    "difftest/tests/coverage-baseline.json",
]


def check_numbers(base: Tree, head: Tree, r: Report) -> None:
    for path, keys in NUMBERS.items():
        old, new = load_json(base, path), load_json(head, path)
        if old is None:
            continue
        if new is None:
            r.fail(path, "removed")
            continue
        bad = []
        for key, direction in keys.items():
            if key not in old:
                continue
            if key not in new:
                bad.append(f"{key} removed")
            elif direction == "up" and new[key] < old[key]:
                bad.append(f"{key} fell from {old[key]} to {new[key]}")
            elif direction == "down" and new[key] > old[key]:
                bad.append(f"{key} rose from {old[key]} to {new[key]}")
            elif direction == "same" and new[key] != old[key]:
                bad.append(f"{key} changed from {old[key]} to {new[key]}")
        r.fail(path, "; ".join(bad)) if bad else r.ok(path)


def check_coverage(base: Tree, head: Tree, r: Report) -> None:
    for path in COVERAGE_BASELINES:
        old, new = load_json(base, path), load_json(head, path)
        if old is None:
            continue
        if new is None:
            r.fail(path, "removed")
            continue
        bad = [
            f"{key} coverage fell from {old[key]}% to {new.get(key)}%"
            for key in ("line", "branch")
            if new.get(key, 0) < old[key]
        ]
        dropped = [f for f in old["files"] if head.exists(f) and f not in new.get("files", [])]
        if dropped:
            bad.append("no longer measured: " + ", ".join(dropped))
        r.fail(path, "; ".join(bad)) if bad else r.ok(path)


def check_accepted(base: Tree, head: Tree, r: Report) -> None:
    path = "books/corpus/accepted.txt"
    old, new = base.read(path), head.read(path)
    if old is None:
        return
    lost = sorted(set(old.split()) - set((new or "").split()))
    if lost:
        r.fail(path, "no longer accepted: " + ", ".join(lost))
    else:
        r.ok(path)


# ── The checks themselves ────────────────────────────────────────────────────


def make_checks(tree: Tree) -> set[str]:
    text = tree.read("Makefile") or ""
    m = re.search(r"^CHECKS\s*:=((?:.*\\\n)*.*)$", text, re.MULTILINE)
    return set(m.group(1).replace("\\\n", " ").split()) if m else set()


def audited_theorems(tree: Tree) -> set[str]:
    paths = tree.matching(["*.lean", "*.sh"])
    tree.preload(paths)
    found = set()
    for p in paths:
        found.update(re.findall(r"^#print axioms\s+(\S+)", tree.read(p) or "", re.MULTILINE))
    return found


COMPARATOR = "books/Books/TypeSoundness/Comparator/config.json"


def check_definitions(base: Tree, head: Tree, r: Report) -> None:
    lost = sorted(make_checks(base) - make_checks(head))
    what = "the targets of `make check`"
    r.fail(what, "no longer run: " + ", ".join(lost)) if lost else r.ok(what)

    lost = sorted(audited_theorems(base) - audited_theorems(head))
    what = "the theorems whose axioms are audited (#print axioms)"
    r.fail(what, "no longer audited: " + ", ".join(lost)) if lost else r.ok(what)

    old, new = load_json(base, COMPARATOR), load_json(head, COMPARATOR)
    if old is not None:
        new = new or {}
        bad = []
        lost = sorted(set(old["theorem_names"]) - set(new.get("theorem_names", [])))
        if lost:
            bad.append("no longer re-checked: " + ", ".join(lost))
        added = sorted(set(new.get("permitted_axioms", [])) - set(old["permitted_axioms"]))
        if added:
            bad.append("newly permitted axioms: " + ", ".join(added))
        for key in ("challenge_module", "solution_module"):
            if new.get(key) != old[key]:
                bad.append(f"{key} changed from {old[key]} to {new.get(key)}")
        r.fail(COMPARATOR, "; ".join(bad)) if bad else r.ok(COMPARATOR)


# ── Counts that may not rise, and one that may not fall ──────────────────────

# (what, files, pattern): the number of matches may not rise
ESCAPE_HATCHES = [
    ("`sorry` in Lean", ["*.lean"], r"\bsorry\b"),
    ("`native_decide` in Lean", ["*.lean"], r"\bnative_decide\b"),
    (
        "axiom declarations in Lean",
        ["*.lean"],
        r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:private|protected|noncomputable|unsafe|partial)[ \t]+)*axiom\b",
    ),
    ("`implemented_by` / `extern` in Lean", ["*.lean"], r"@\[\s*(?:implemented_by|extern)\b"),
    (
        "kernel checks switched off in Lean",
        ["*.lean", "*/lakefile.toml"],
        r"skipKernelTC|debug\.skip",
    ),
    ("`noqa` in Python", ["*.py", "bin/*"], r"#\s*noqa"),
    ("`type: ignore` in Python", ["*.py", "bin/*"], r"#\s*type:\s*ignore"),
    ("`pragma: no cover` in Python", ["*.py", "bin/*"], r"pragma:\s*no\s*cover"),
    ("skipped Python tests", ["*.py"], r"pytest\.(?:mark\.)?(?:skip|skipif|xfail)\b|importorskip"),
    (
        "`rubocop:disable` in Ruby",
        ["*.rb", "desugar/bin/*", "Gemfile"],
        r"rubocop:(?:disable|todo)",
    ),
    ("`:nocov:` in Ruby", ["*.rb", "desugar/bin/*"], r":nocov:"),
    ("skipped Ruby tests", ["*/test/*.rb"], r"^\s*skip\b"),
    ("`shellcheck disable` in shell scripts", ["*.sh"], r"shellcheck\s+disable"),
    ("ignored errors in the workflows", [".github/*"], r"continue-on-error|\|\|\s*true"),
    ("ignored errors in the Makefile", ["Makefile"], r"^\t-|\|\|\s*true"),
]

TESTS = ("test functions", ["*.py", "*/test/*.rb"], r"^\s*def test_|define_method\(:\"test_")


def count(tree: Tree, globs: list[str], pattern: str) -> dict[str, int]:
    rx = re.compile(pattern, re.MULTILINE)
    paths = tree.matching(globs)
    tree.preload(paths)
    counts = {p: len(rx.findall(tree.read(p) or "")) for p in paths}
    return {p: n for p, n in counts.items() if n}


def per_file(old: dict[str, int], new: dict[str, int], rising: bool) -> str:
    moved = []
    for p in sorted(set(old) | set(new)):
        a, b = old.get(p, 0), new.get(p, 0)
        if (b > a) if rising else (b < a):
            moved.append(f"{p} {a}->{b}")
    return ", ".join(moved)


def check_counts(base: Tree, head: Tree, r: Report) -> None:
    for what, globs, pattern in ESCAPE_HATCHES:
        old, new = count(base, globs, pattern), count(head, globs, pattern)
        a, b = sum(old.values()), sum(new.values())
        if b > a:
            r.fail(what, f"rose from {a} to {b} ({per_file(old, new, rising=True)})")
        else:
            r.ok(f"{what} ({b})")
    what, globs, pattern = TESTS
    old, new = count(base, globs, pattern), count(head, globs, pattern)
    a, b = sum(old.values()), sum(new.values())
    if b < a:
        r.fail(what, f"fell from {a} to {b} ({per_file(old, new, rising=False)})")
    else:
        r.ok(f"{what} ({b})")


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "--base", default="origin/main", help="the version to compare with (default: origin/main)"
    )
    ap.add_argument("--head", default=None, help="the version to check (default: the working tree)")
    args = ap.parse_args(argv)

    base, head = Tree(args.base), Tree(args.head)
    r = Report()
    check_numbers(base, head, r)
    check_coverage(base, head, r)
    check_accepted(base, head, r)
    check_definitions(base, head, r)
    check_counts(base, head, r)

    print(f"{head.name()} against {base.name()}")
    print("\n".join(r.lines))
    print()
    if r.failures:
        print(f"CHECKS WEAKENED -- {len(r.failures)} of the above moved the wrong way.")
        print("A change that must do this needs a maintainer's review and merge.")
        return 1
    print("CHECKS NOT WEAKENED")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
