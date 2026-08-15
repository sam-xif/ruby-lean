"""Build the advisory corpus (R1): one program per advisory shape.

    python3 -m difftest advisory-fuzz --brew <path> -n 800

`-n` counts (advisory × version) pairs. Unlike the domain tier this does **not**
batch several inputs' worth of *shapes* into one program: a gate anywhere
refuses the whole program (`homebrew/HANDOFF.md`), and §3.3 of
`nontrivial-target.md` predicts this corpus finds gates the harvested one never
touches. One shape per program means a gating shape costs its own rows and no
others, and the gate count is then a measurement rather than a loss.
"""

from __future__ import annotations

import json
import os

from ..tier0.rspec_harvest import (BLANK_STUB, SORBET_REQUIRE, _ruby, build_prefix)
from . import gen, harness

FEATURE = "vulns/vulnerability"
# `vulnerability.rb` references `::Version` without requiring it — Homebrew's
# boot path supplies it, and `PLAN.md` §2 counts it as in-slice. Link it in
# front, the way the domain tier's `pairs` harness does.
EXTRA_FEATURES = ["version"]


def build(brew_root: str, out_dir: str, n: int, seed: int,
          ruby: str | None = None) -> dict:
    ruby = ruby or _ruby()
    os.makedirs(out_dir, exist_ok=True)
    prefix = build_prefix(FEATURE, brew_root, ruby)
    for extra in EXTRA_FEATURES:
        prefix = build_prefix(extra, brew_root, ruby) + prefix
    pre = SORBET_REQUIRE + BLANK_STUB
    manifest = []
    for c in gen.cases(n, seed):
        src = harness.program(c["id"], gen.to_ruby(c["advisory"]), c["versions"],
                              prefix, pre, c["mutations"])
        with open(os.path.join(out_dir, c["id"] + ".rb"), "w", encoding="utf-8") as f:
            f.write(src)
        manifest.append({"id": c["id"], "inputs": len(c["versions"]),
                         "mutations": c["mutations"], "seed": seed})
    with open(os.path.join(out_dir, "manifest.json"), "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=1)
        f.write("\n")
    return {"programs": len(manifest),
            "inputs": sum(m["inputs"] for m in manifest), "out": out_dir}
