#!/usr/bin/env python3
"""Straight-line controls for `probes/loop_strictness.py`.

A `validate=false` on a loop probe has two possible causes and the table cannot tell
them apart: (a) `Judge.while'`'s fixed-point premise rejected the body, or (b) the
checker cannot type that body at all, loop or no loop (an unclimbed rung, a missing
`PrimSig` row, a `Ty` gap). Each probe here is the same body **without** the loop.
"""
import json, os, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from loop_strictness import EXPORT, RAT, cruby, srb

PROBES = [
  ("c-float",     "float arithmetic, no loop", "x = 0.0\nx = x + 0.5\nx\n"),
  ("c-float-cmp", "float comparison, no loop", "x = 0.0\nx < 1.0\n"),
  ("c-nested",    "nested body's statements, no loops",
   "i = 0\nt = 0\nj = 0\nt = t + 1\nj = j + 1\ni = i + 1\nt\n"),
  ("c-newlocal",  "a local introduced then used, no loop", "i = 0\ny = i\ni\n"),
  ("c-push",      "Array#push, no loop", "a = []\na.push(1)\na.length\n"),
  ("c-concat",    "array + array, no loop", "a = []\na = a + [1]\na.length\n"),
  ("c-arr-lit",   "a non-empty array literal", "a = [1]\na.length\n"),
  ("c-break-each","break in an each block (corpus 187's shape)",
   "s = 0\n[1, 2, 3].each do |x|\n  break if x == 3\n  s = s + x\nend\ns\n"),
  ("c-inc",       "the accepted increment body, no loop", "i = 0\ni = i + 1\ni\n"),
]

def main():
    scratch = tempfile.mkdtemp(prefix="loopctl-")
    for i, (pid, desc, rb) in enumerate(PROBES):
        with tempfile.NamedTemporaryFile("w", suffix=".rb", delete=False) as f:
            f.write(rb); path = f.name
        prog = json.loads(subprocess.run([EXPORT, path], capture_output=True,
                                         text=True, check=True).stdout)
        os.unlink(path)
        json.dump({"id": pid, "tier": 99, "description": desc, "program": prog,
                   "expect_validate": True, "false_reason": None},
                  open(os.path.join(scratch, f"{i:03d}-{pid}.json"), "w"))
        open(os.path.join(scratch, f"{i:03d}-{pid}.rb"), "w").write(rb)
    out = subprocess.run([os.path.join(RAT, ".lake/build/bin/ratchet"), scratch],
                         capture_output=True, text=True)
    val = {}
    for line in out.stdout.split("\n"):
        if line.startswith("tier 99 "):
            val[line.split()[2].rstrip(":")] = "true" if "validate=true" in line else "false"
    print(f"{'control':14} {'validate':9} {'CRuby':12} srb")
    print("-" * 80)
    for pid, desc, rb in PROBES:
        print(f"{pid:14} {val.get(pid,'?'):9} {cruby(rb):12} {srb(rb)}")

if __name__ == "__main__":
    main()
