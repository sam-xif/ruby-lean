#!/usr/bin/env python3
"""Round three: does hoisting the declaration out of the loop recover the pattern?

Each probe is a round-one/two rejection with the body's new locals **pre-initialised**
before the loop, so that `Judge.while'`'s `Γb = Γ` has a fixed point to land on. If these
pass, the restriction is "declare loop-body locals up front", not "no imperative loops".
"""
import json, os, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from loop_strictness import EXPORT, RAT, cruby, srb

PROBES = [
  ("hoist-newlocal", "new-local, hoisted",
   "i = 0\ny = 0\nwhile i < 3\n  y = i\n  i = i + 1\nend\ny\n"),
  ("hoist-nested",   "nested loops, inner counter hoisted",
   "i = 0\nt = 0\nj = 0\nwhile i < 3\n  j = 0\n  while j < 3\n    t = t + 1\n    j = j + 1\n  end\n  i = i + 1\nend\nt\n"),
  ("hoist-swap",     "swap, temp hoisted",
   "a = 1\nb = 2\nt = 0\ni = 0\nwhile i < 3\n  t = a\n  a = b\n  b = t\n  i = i + 1\nend\na\n"),
  ("hoist-condassign","condition that assigns, target hoisted",
   "i = 0\nj = 0\nwhile (j = i) < 3\n  i = i + 1\nend\ni\n"),
  ("cond-and-ctl",   "compound `&&` condition -- is the synthetic temp the cause?",
   "x = 1\ni = 0\nwhile i < 3 && x > 0\n  i = i + 1\nend\ni\n"),
  ("cond-and-straight","the same `&&` outside a loop (control)",
   "x = 1\ni = 0\nb = i < 3 && x > 0\nb\n"),
  ("cond-single",    "the same loop with a single comparison (control)",
   "x = 1\ni = 0\nwhile i < 3\n  i = i + 1\nend\ni\n"),
  ("hoist-widen",    "widen-nil, declared as the wide type up front is not expressible; "
                     "declared Integer instead",
   "x = 0\ni = 0\nwhile i < 3\n  x = i\n  i = i + 1\nend\nx + 1\n"),
]

def main():
    scratch = tempfile.mkdtemp(prefix="loopwa-")
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
    print(f"{'probe':20} {'validate':9} {'CRuby':12} srb")
    print("-" * 88)
    for pid, desc, rb in PROBES:
        print(f"{pid:20} {val.get(pid,'?'):9} {cruby(rb):12} {srb(rb)}")

if __name__ == "__main__":
    main()
