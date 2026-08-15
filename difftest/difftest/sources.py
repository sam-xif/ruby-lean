"""Corpus case sources: persisted .rb corpora loaded as TestCases.

Tier 0 is the conformance-corpus tier. Its first source is MRI's own
bootstraptest suite, as harvested by the desugar harness
(`../harness/desugar-dt/bin/harvest_bootstraptest`) — no translation needed,
the harvested cases are already self-contained single-file Ruby. Validity is
enforced at run time by the existing control gate in `run_case` (parse check,
timeout, determinism double-run), so unusable cases are excluded with reasons
rather than pre-filtered here.
"""

from __future__ import annotations

import dataclasses
import json
from pathlib import Path

from .testcase import TestCase

BASE = Path(__file__).resolve().parents[1]  # ruby/difftest/
BOOTSTRAPTEST_DIR = (
    BASE.parent / "harness" / "desugar-dt" / "corpus" / "bootstraptest"
)

SORBET_DIR = BASE / "corpus" / "sorbet"

# The Sorbet corpus is organized by *which part of Sorbet's design* a program
# probes, not by Ruby construct — the taxonomy is the one in
# `../docs/semantics/types-and-preservation.md` §A, because the object of study
# is the type system, not the language.
SORBET_CATEGORIES = {
    "sig-basic": "plain sigs; both halves quiet, or both firing on one defect (§A.5)",
    "narrowing": "flow-sensitive/occurrence typing and its documented limits (§A.2)",
    "assertions": "the T.let/T.cast/T.must/T.unsafe static-vs-runtime table (§A.3)",
    "untyped-boundary": "T.untyped and the no-sig gradual boundary; blame (§A.5, §B.5)",
    "escape-hatches": "the unsoundness catalogue: holes Sorbet accepts by design (§A.3)",
    "structs-enums": "T::Struct / T::Enum, incl. the checked/unchecked asymmetry (§A.1)",
    # The only category with no annotations, and deliberately so — see
    # `test_every_program_requires_sorbet_runtime` for why it is exempt from the
    # `require "sorbet-runtime"` rule.
    "p0-fragment": (
        "plain Ruby inside the P0 static-checker fragment; exercises the "
        "check-vs-srb relation and its pinned zeros "
        "(static-soundness-poc.md §7)"
    ),
    "generics": "runtime-erased generics — statically checked, no runtime backstop (§A.6)",
}

# Declared expectations recorded in each sidecar, validated by `difftest sorbet
# check`. Kept as closed vocabularies so a typo in a sidecar is an error rather
# than a silently-unmatched string.
STATIC_EXPECT = ("clean", "errors")
RUNTIME_EXPECT = (
    "value",  # terminates normally
    "sorbet_error",  # sorbet-runtime enforcement raised (the "blame" outcome)
    "ruby_error",  # a genuine Ruby-level error escaped (Sorbet gave no backstop)
)

HARVEST_RECIPE = """\
The bootstraptest corpus is harvested on demand (not vendored). To fetch it:
  git clone --depth 1 --filter=blob:none --sparse https://github.com/ruby/ruby /tmp/ruby
  (cd /tmp/ruby && git sparse-checkout set bootstraptest)
  ../harness/desugar-dt/bin/harvest_bootstraptest /tmp/ruby/bootstraptest"""


def load_corpus_cases(corpus: Path, default_tier: int = -1) -> list[TestCase]:
    """Load a replayable corpus directory: every .rb file, with the optional
    same-stem .json sidecar as provenance (the tier-3 layout)."""
    cases = []
    for path in sorted(corpus.rglob("*.rb")):
        meta_path = path.with_suffix(".json")
        meta = json.loads(meta_path.read_text()) if meta_path.exists() else {}
        cases.append(
            TestCase(
                id=str(path.relative_to(corpus)),
                source=path.read_text(),
                tier=meta.get("tier", default_tier),
                provenance={**meta, "path": str(path)},
            )
        )
    return cases


SLICE_DIR = BASE / "corpus" / "homebrew-slice"

SLICE_HARVEST_RECIPE = """The Homebrew-slice corpus is generated, not vendored (each program
embeds ~20 KB of upstream Homebrew). To build it:

  python3 -m difftest harvest-rspec --brew /path/to/Homebrew/brew"""


def load_slice_corpus(corpus: Path | None = None) -> list[TestCase]:
    """Homebrew's own RSpec examples for the version + vulnerability slice,
    mechanically rewritten into plain-Ruby assertion programs (W4a / N36).

    Each program prints, per expectation, the actual value *and* the matcher's
    verdict — tier 0 asks whether CRuby and the model agree, not whether
    Homebrew's suite passes, so a model bug that changes a value is caught even
    where the verdict would agree either way.
    """
    corpus = Path(corpus) if corpus else SLICE_DIR
    if not corpus.is_dir():
        raise FileNotFoundError(f"no slice corpus at {corpus}\n{SLICE_HARVEST_RECIPE}")
    manifest: dict[str, dict] = {}
    manifest_path = corpus / "manifest.json"
    if manifest_path.exists():
        manifest = {e["id"]: e for e in json.loads(manifest_path.read_text())}
    cases = []
    for path in sorted(corpus.glob("*.rb")):
        meta = manifest.get(path.stem, {"id": path.stem})
        cases.append(
            TestCase(
                id=f"slice/{path.stem}",
                source=path.read_text(),
                tier=0,
                provenance={"suite": "homebrew-slice", **meta},
            )
        )
    if not cases:
        raise FileNotFoundError(f"no .rb cases under {corpus}\n{SLICE_HARVEST_RECIPE}")
    return cases


DOMAIN_DIR = BASE / "corpus" / "domain-fuzz"

DOMAIN_RECIPE = """The domain-fuzz corpus is generated, not vendored. To build it:

  python3 -m difftest domain-fuzz --brew /path/to/Homebrew/brew -n 10000"""


def load_domain_corpus(corpus: Path | None = None) -> list[TestCase]:
    """Batched harness programs over generated version/semver/purl/URL inputs
    (W4d). Each program prints one line per input, so the number of *cases* is
    small and the number of compared observations is large."""
    corpus = Path(corpus) if corpus else DOMAIN_DIR
    if not corpus.is_dir():
        raise FileNotFoundError(f"no domain corpus at {corpus}\n{DOMAIN_RECIPE}")
    manifest: dict[str, dict] = {}
    mp = corpus / "manifest.json"
    if mp.exists():
        manifest = {e["id"]: e for e in json.loads(mp.read_text())}
    cases = [
        TestCase(id=f"domain/{p.stem}", source=p.read_text(), tier=0,
                 provenance={"suite": "domain-fuzz", **manifest.get(p.stem, {})})
        for p in sorted(corpus.glob("*.rb"))
    ]
    if not cases:
        raise FileNotFoundError(f"no .rb cases under {corpus}\n{DOMAIN_RECIPE}")
    return cases


ADVISORY_DIR = BASE / "corpus" / "advisory-fuzz"

ADVISORY_RECIPE = """The advisory-fuzz corpus is generated, not vendored. To build it:

  python3 -m difftest advisory-fuzz --brew /path/to/Homebrew/brew -n 800"""


def load_advisory_corpus(corpus: Path | None = None) -> list[TestCase]:
    """The input-parameterized driver over generated OSV advisory *shapes*
    (R1 of `homebrew/nontrivial-target.md` §6). One program per shape, several
    versions each — deliberately unbatched across shapes, because a gate
    refuses a whole program and this corpus is expected to find gates."""
    corpus = Path(corpus) if corpus else ADVISORY_DIR
    if not corpus.is_dir():
        raise FileNotFoundError(f"no advisory corpus at {corpus}\n{ADVISORY_RECIPE}")
    manifest: dict[str, dict] = {}
    mp = corpus / "manifest.json"
    if mp.exists():
        manifest = {e["id"]: e for e in json.loads(mp.read_text())}
    cases = [
        TestCase(id=f"advisory/{p.stem}", source=p.read_text(), tier=0,
                 provenance={"suite": "advisory-fuzz", **manifest.get(p.stem, {})})
        for p in sorted(corpus.glob("*.rb"))
    ]
    if not cases:
        raise FileNotFoundError(f"no .rb cases under {corpus}\n{ADVISORY_RECIPE}")
    return cases


def load_sorbet_corpus(corpus: Path | None = None) -> list[TestCase]:
    """Load the Sorbet-annotated corpus (tier 4) as TestCases.

    Every program is self-contained and `require "sorbet-runtime"` itself, so
    the *control* exercises Sorbet's runtime enforcement with no wrapper
    changes. Consequence, stated rather than hidden: the Lean SUT gates every
    one of these on `require` until the sorbet-runtime prelude shim exists —
    that gap is the point of the next phase, not a defect in the corpus.
    """
    return load_corpus_cases(Path(corpus) if corpus else SORBET_DIR, default_tier=4)


def load_bootstraptest(corpus: Path | None = None) -> list[TestCase]:
    """Load the harvested bootstraptest corpus as tier-0 cases.

    manifest.json (written by the harvester) contributes per-case provenance:
    the original bootstraptest file, the assert form, and the expected value.
    """
    corpus = Path(corpus) if corpus else BOOTSTRAPTEST_DIR
    if not corpus.is_dir():
        raise FileNotFoundError(f"no bootstraptest corpus at {corpus}\n{HARVEST_RECIPE}")
    manifest: dict[str, dict] = {}
    manifest_path = corpus / "manifest.json"
    if manifest_path.exists():
        manifest = {e["file"]: e for e in json.loads(manifest_path.read_text())}
    cases = []
    for path in sorted(corpus.glob("*.rb")):
        meta = manifest.get(path.name, {"file": path.name})
        cases.append(
            TestCase(
                id=f"bootstraptest/{path.stem}",
                source=path.read_text(),
                tier=0,
                provenance={"suite": "bootstraptest", **meta},
            )
        )
    if not cases:
        raise FileNotFoundError(f"no .rb cases under {corpus}\n{HARVEST_RECIPE}")
    return cases


# ─── The regressions corpus: cases that once disagreed ──────────────────────
#
# Written by `campaign.py` every time a generative campaign shrinks a
# disagreement, and — until this tier existed — read by nothing. A defect could
# be found, minimized, filed here, and then never executed again, which is how a
# *known* wrong answer can sit behind a green ratchet: the two generative tiers
# re-draw their programs every run, so whether they rediscover it is a matter of
# the sample. `N41` is the entry; the `coerce` defect is the case in point.
#
# Every case carries a **status**, and the tier checks the actual verdict against
# it. That is what makes the corpus a ratchet in both directions:
#
#   * `open`  — a known wrong answer, not yet fixed. Expected to DISAGREE. If it
#               agrees, someone fixed it and the sidecar is now a lie.
#   * `fixed` — was a wrong answer, now correct. Expected to AGREE. If it
#               disagrees, that is a regression in the classic sense.
#
# There is no third status on purpose: a case here either reproduces a live
# defect or guards a dead one.
REGRESSIONS_DIR = BASE / "corpus" / "regressions"

REGRESSION_STATUS = ("open", "fixed")

# A case with no sidecar is `open`: the campaign writes the .rb at the moment a
# disagreement is confirmed, which is precisely when the defect is live. The
# default therefore cannot be wrong at write time, and going green later is what
# forces the sidecar to be written.
REGRESSION_DEFAULT_STATUS = "open"


def load_regressions_corpus(corpus: Path | None = None) -> list[TestCase]:
    """Load `corpus/regressions/` — minimized reproducers of past disagreements.

    Unlike every other corpus here, this one is *append-only by machine*: the
    campaign writes to it. An empty directory is not an error (a project with no
    known-open defects is the goal), so this returns `[]` rather than raising.
    """
    corpus = Path(corpus) if corpus else REGRESSIONS_DIR
    if not corpus.is_dir():
        return []
    cases = []
    for case in load_corpus_cases(corpus, default_tier=-1):
        status = case.provenance.get("status", REGRESSION_DEFAULT_STATUS)
        if status not in REGRESSION_STATUS:
            raise ValueError(
                f"regressions case {case.id!r} has status {status!r}; "
                f"expected one of {REGRESSION_STATUS}"
            )
        cases.append(
            dataclasses.replace(case, provenance={**case.provenance, "status": status})
        )
    return cases


# What a regressions case's actual verdict means, given the status it declares.
# Only `regressed` and `unexpectedly_fixed` are failures — the first is a defect
# reintroduced, the second is bookkeeping that has fallen behind reality, and
# both need a human. `still_open` is the expected state of a known defect and
# must NOT redden the run, or the corpus could never hold one.
REGRESSION_OUTCOMES = {
    "held": "was fixed and still agrees",
    "still_open": "known-open defect, still reproduces",
    "regressed": "was fixed and now disagrees — a real regression",
    "unexpectedly_fixed": "known-open defect now agrees — flip its sidecar to fixed",
    "gated": "the SUT now gates this program, so it no longer pins anything",
    "unusable": "the control could not run it (parse error / timeout / nondeterminism)",
}

REGRESSION_FAILURES = ("regressed", "unexpectedly_fixed")


def regression_outcome(status: str, verdict_value: str) -> str:
    """Reconcile a declared status against an observed verdict.

    A **gate** is deliberately not a failure and deliberately not a pass. For an
    `open` case it means the wrong answer became a refusal, which is an
    improvement the sidecar should record but not one this function can verify;
    for a `fixed` case it means the guard has stopped guarding. Either way the
    honest report is "this case no longer tests what it was filed to test".
    """
    if verdict_value in ("control_invalid", "harness_error"):
        return "unusable"
    if verdict_value == "sut_unsupported":
        return "gated"
    disagreed = verdict_value == "disagree"
    if status == "open":
        return "still_open" if disagreed else "unexpectedly_fixed"
    return "regressed" if disagreed else "held"
