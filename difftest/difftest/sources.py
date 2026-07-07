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
