#!/usr/bin/env python3
"""record_baseline.py -- freeze the current pipeline verdicts into each rung's meta.

Two fields, and both are **ratchets**: once recorded, a rung that changes verdict is a
regression the runner reports, not a silent drift.

* `expect_sorbet` -- does `srb` typecheck the annotated source clean? This is *not*
  always `true`, and the interesting rungs are the ones where it is not:
  `054-fun-body-mismatch` declares `Integer` for a body that adds `true`, and Sorbet
  rejecting it is the rung's content. `sorbet_note` records the first diagnostic so the
  reason is in the file rather than in a build directory.
* `known_upstream_failure` -- a stage before the emitter (the strip stack, the
  desugarer) that declines. Recorded so `lake exe ratchetd` can exit non-zero on a *new*
  one while staying green on the eleven `slice/` rungs whose whole-file sources
  `difftest/ruby/sig_strip.rb` cannot strip (`T::Struct`, `T::Helpers`).

Run after `scripts/build_corpus.py`, read the diff before committing it.
"""
from __future__ import annotations

import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def gist(diags: list[str]) -> str | None:
    for d in diags:
        m = re.search(r"\.rb:\d+: (.*?)(?: https://srb\.help.*)?$", d)
        if m:
            return m.group(1)[:160]
    return None


def main(argv: list[str]) -> int:
    build = os.path.join(ROOT, "build")
    corpus = os.path.join(ROOT, "corpus")
    changed = 0
    for f in sorted(glob.glob(os.path.join(build, "*.rung.json"))):
        rec = json.load(open(f))
        mp = os.path.join(corpus, rec["base"] + ".meta.json")
        meta = json.load(open(mp))
        before = json.dumps(meta, sort_keys=True)
        meta["expect_sorbet"] = bool(rec.get("srb_clean"))
        note = gist(rec.get("srb_diagnostics", [])) if not rec.get("srb_clean") else None
        if note:
            meta["sorbet_note"] = note
        else:
            meta.pop("sorbet_note", None)
        if rec.get("stage") != "done":
            meta["known_upstream_failure"] = f"{rec.get('stage')}: {rec.get('error','')[:120]}"
        else:
            meta.pop("known_upstream_failure", None)
        if json.dumps(meta, sort_keys=True) != before:
            with open(mp, "w") as fh:
                json.dump(meta, fh, indent=2)
                fh.write("\n")
            changed += 1
    print(f"recorded baseline into {changed} rung metas")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
