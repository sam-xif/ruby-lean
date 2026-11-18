#!/usr/bin/env python3
"""Check the harvested bootstraptest corpus against the conformance baseline.

    scripts/check-corpus-baseline.py            # what `make conformance-corpus` runs
    scripts/check-corpus-baseline.py CORPUS_DIR # a corpus somewhere else

`difftest/coverage-baseline.json` records `ran`: how many programs the tier-0
corpus holds. The corpus is harvested on demand and never stored in this
repository, so a harvest change leaves the baseline describing a corpus that is
no longer there, and `make conformance` says so only after it has built the
model and replayed every program. This says it from the corpus alone, in
seconds; `make conformance` runs it first, so it is part of `make check`.

Exit status is 0 when they agree, 1 when they do not, and 2 when there is no
corpus to check (run `make conformance` once to harvest one).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "difftest" / "coverage-baseline.json"
CORPUS = ROOT / "desugar" / "corpus" / "bootstraptest"


def main(argv: list[str]) -> int:
    # The comparison rule lives beside the loader it belongs to (difftest/sources.py),
    # so that the corpus this checks and the corpus a run replays cannot drift apart.
    sys.path.insert(0, str(ROOT / "difftest"))
    from difftest.sources import HARVEST_RECIPE, bootstraptest_baseline_problems

    corpus = Path(argv[0]) if argv else CORPUS
    programs = len(list(corpus.glob("*.rb")))
    if programs == 0:
        print(f"no bootstraptest corpus at {corpus}\n{HARVEST_RECIPE}", file=sys.stderr)
        return 2

    baseline = json.loads(BASELINE.read_text())
    problems = bootstraptest_baseline_problems(corpus, baseline)
    print("the harvested corpus against the conformance baseline")
    print(f"  programs  {programs} in {corpus}")
    print(
        f"  recorded  ran {baseline.get('ran')}  agree {baseline.get('agree')}  "
        f"sut_unsupported {baseline.get('sut_unsupported')}"
    )

    if not problems:
        print("\nCORPUS OK -- the corpus is the one the baseline was measured on.")
        return 0

    print()
    for problem in problems:
        print(f"CORPUS FAILED -- {problem}")
    print(
        f"\n  A harvest only adds programs, so remove {corpus} first, harvest again\n"
        "  from the pinned tag, then re-measure and record the numbers with\n"
        "    scripts/check-conformance.sh --save .make/conformance"
    )
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
