"""A domain generator for the slice's *inputs* — version strings, semver
strings, package URLs and purls (W4d).

The premise, from `homebrew/PLAN.md` §W4d: for this slice the highest-value
fuzzing is not random ASTs but random **inputs**. A random program mostly
exercises the machine; a random version string exercises the tokenizer, the
comparison chain, the URL parsers and the regex engine, which is where the
model and CRuby can actually differ.

Two design choices worth stating:

* **Grammar-based, not character-random.** The shapes come from the ones the
  spec suite already contains (dotted numerics, `-rc1`, `_1`, `R13B`, date
  stamps, platform suffixes, forge URLs), because those are the shapes the
  parsers branch on. A uniformly random string almost always lands in the same
  "no match" arm and tests nothing.
* **Batched, not one program per input.** Each emitted program carries a few
  hundred inputs and prints one line per input, so 10,000 inputs cost ~50 runs
  of a 25 KB program rather than 10,000. The comparison is still per-line.

Deterministic given a seed, so a disagreement replays.
"""

from __future__ import annotations

import random

# ── the alphabets, taken from shapes in the spec suite ─────────────────────
PRE_WORDS = ["alpha", "beta", "rc", "pre", "a", "b", "c", "RC", "dev", "p",
             "post", "final", "stable", "src", "bin", "dist"]
SEPS = [".", "-", "_", ""]
PLATFORMS = ["x86_64", "i386", "darwin", "linux", "mingw32", "mswin32", "java",
             "win32", "win64", "universal"]
EXTS = ["tar.gz", "tar.bz2", "tar.xz", "tgz", "zip", "gem", "crate", "jar",
        "nupkg", "whl", "tar"]
NAMES = ["foo", "bar-baz", "libx", "ruamel.yaml", "gradle-profiler", "bfg",
         "Newtonsoft.Json", "@scope/pkg", "serde", "aeson", "abc"]
FORGES = [
    "https://github.com/{n}/{n}/archive/refs/tags/{v}.tar.gz",
    "https://github.com/{n}/{n}/releases/download/{v}/{n}-{v}.zip",
    "https://rubygems.org/downloads/{n}-{v}.gem",
    "https://registry.npmjs.org/{n}/-/{n}-{v}.tgz",
    "https://files.pythonhosted.org/packages/aa/bb/cc/{n}-{v}.tar.gz",
    "https://repo1.maven.org/maven2/org/{n}/{n}/{v}/{n}-{v}.jar",
    "https://static.crates.io/crates/{n}/{n}-{v}.crate",
    "https://cran.r-project.org/src/contrib/{n}_{v}.tar.gz",
    "https://hackage.haskell.org/package/{n}-{v}",
    "https://sourceforge.net/projects/{n}/files/{n}-{v}.{e}/download",
    "https://brew.sh/{n}-{v}.{e}",
    "https://example.org/{n}/{v}/{n}.{e}",
]


def _num(r: random.Random) -> str:
    return str(r.choice([0, 1, 2, 3, 7, 9, 10, 12, 20, 99, 100, 2024, 194]))


def numeric(r: random.Random) -> str:
    return ".".join(_num(r) for _ in range(r.randint(1, 4)))


def prerelease(r: random.Random) -> str:
    w = r.choice(PRE_WORDS)
    tail = "" if r.random() < 0.3 else _num(r)
    return f"{r.choice(SEPS)}{w}{r.choice(['', '.'])}{tail}"


def version_string(r: random.Random) -> str:
    """A Homebrew-`Version`-shaped string: the tokenizer's whole domain."""
    kind = r.random()
    if kind < 0.10:
        return f"R{_num(r)}B{'' if r.random() < 0.5 else _num(r)}"
    if kind < 0.18:
        return f"{r.choice(['', 'v', 'V'])}{r.randint(2000, 2030)}-{r.randint(1, 12):02d}-{r.randint(1, 28):02d}"
    if kind < 0.24:
        return "_".join(_num(r) for _ in range(r.randint(2, 3)))
    s = r.choice(["", "v", "V", "r"]) + numeric(r)
    if r.random() < 0.45:
        s += prerelease(r)
    if r.random() < 0.15:
        s += f"-{_num(r)}"
    if r.random() < 0.10:
        s += f"-{r.choice(PLATFORMS)}"
    return s


def semver_string(r: random.Random) -> str:
    """Valid SemVer 2.0 most of the time, deliberately invalid sometimes — the
    invalid half is where `Semver.compare` and `Version#<=>` are most likely to
    part company."""
    if r.random() < 0.12:
        return version_string(r)  # not a semver at all
    s = r.choice(["", "v", "V"]) + ".".join(_num(r) for _ in range(r.randint(1, 3)))
    if r.random() < 0.5:
        ids = [r.choice(PRE_WORDS + [_num(r)]) for _ in range(r.randint(1, 3))]
        s += "-" + ".".join(str(i) for i in ids)
    if r.random() < 0.3:
        s += "+" + ".".join(r.choice(["exp", "sha", "build", _num(r)])
                            for _ in range(r.randint(1, 2)))
    return s


def url_string(r: random.Random) -> str:
    return r.choice(FORGES).format(n=r.choice(NAMES), v=version_string(r),
                                   e=r.choice(EXTS))


def purl_string(r: random.Random) -> str:
    eco = r.choice(["gem", "npm", "pypi", "maven", "cargo", "hex", "nuget", "golang"])
    name = r.choice(NAMES)
    ver = semver_string(r)
    s = f"pkg:{eco}/{name}"
    if r.random() < 0.85:
        s += f"@{ver}"
    if r.random() < 0.15:
        s += "?arch=x86_64"
    if r.random() < 0.10:
        s += "#subpath"
    return s


GENERATORS = {
    "version": version_string,
    "semver": semver_string,
    "url": url_string,
    "purl": purl_string,
}


def sample(kind: str, n: int, seed: int) -> list[str]:
    r = random.Random(seed)
    gen = GENERATORS[kind]
    return [gen(r) for _ in range(n)]
