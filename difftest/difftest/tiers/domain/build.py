"""Build the domain-fuzz corpus: batched harness programs over generated inputs.

    python3 -m difftest domain-fuzz --brew <path> -n 10000

`-n` counts **inputs**, not programs: they are batched (default 250 per
program), because each program carries a ~25 KB library prefix and the
comparison is per printed line either way. That is what makes 10,000 inputs a
few dozen subprocess pairs instead of ten thousand.
"""

from __future__ import annotations

import json
import os

from ..tier0.rspec_harvest import (BLANK_STUB, SORBET_REQUIRE, _ruby, build_prefix)
from . import harness, version_gen

# 250 inputs in one program overran the SUT timeout on the two Version-heavy
# harnesses (the control took 0.1 s, the model 10 s+). The batch exists to
# amortize the 25 KB library prefix, not to be as large as possible.
BATCH = 50


def build(brew_root: str, out_dir: str, n: int, seed: int,
          ruby: str | None = None, batch: int = BATCH) -> dict:
    ruby = ruby or _ruby()
    os.makedirs(out_dir, exist_ok=True)
    manifest = []
    per_harness = max(1, n // len(harness.HARNESSES))
    for hname, h in sorted(harness.HARNESSES.items()):
        prefix = build_prefix(h["feature"], brew_root, ruby)
        for extra in h.get("extra_features", []):
            prefix = build_prefix(extra, brew_root, ruby) + prefix
        inputs = version_gen.sample(h["kind"], per_harness, seed + hash(hname) % 9973)
        for b in range(0, len(inputs), batch):
            chunk = inputs[b:b + batch]
            pre = SORBET_REQUIRE + BLANK_STUB
            src = harness.program(hname, chunk, prefix, pre)
            ident = f"{hname}-{seed}-{b // batch:03d}"
            with open(os.path.join(out_dir, ident + ".rb"), "w", encoding="utf-8") as f:
                f.write(src)
            manifest.append({"id": ident, "harness": hname, "kind": h["kind"],
                             "inputs": len(chunk), "seed": seed})
    with open(os.path.join(out_dir, "manifest.json"), "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=1)
        f.write("\n")
    return {"programs": len(manifest),
            "inputs": sum(m["inputs"] for m in manifest), "out": out_dir}
