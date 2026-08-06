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
