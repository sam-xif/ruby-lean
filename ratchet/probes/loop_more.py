#!/usr/bin/env python3
"""Round two: the remaining `while`-shape questions — other loop heads, a condition
that assigns, a branching body, and a body that calls a user method."""
import json, os, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from loop_strictness import EXPORT, RAT, cruby, srb

PROBES = [
  ("cond-assign",  "the `while (x = …)` idiom: the condition assigns",
   "i = 0\nwhile (j = i) < 3\n  i = i + 1\nend\ni\n"),
  ("cond-narrow",  "the condition narrows a local; body uses it",
   "x = 1\ni = 0\nwhile i < 3 && x > 0\n  i = i + 1\nend\ni\n"),
  ("if-body",      "an `if` in the body, both arms assigning the counter",
   "i = 0\nwhile i < 4\n  if i == 1\n    i = i + 2\n  else\n    i = i + 1\n  end\nend\ni\n"),
  ("call-body",    "the body calls a user-defined method",
   "def f(x)\n  x + 1\nend\ni = 0\nwhile i < 3\n  i = f(i)\nend\ni\n"),
  ("dowhile",      "`begin … end while` (a separate head, `Expr.dowhile`)",
   "i = 0\nbegin\n  i = i + 1\nend while i < 3\ni\n"),
  ("for-range",    "`for i in 0..2` (a separate head, `Expr.for'`)",
   "t = 0\nfor i in 0..2\n  t = t + i\nend\nt\n"),
  ("times",        "`3.times { }` — a block, not a loop head",
   "t = 0\n3.times do |i|\n  t = t + i\nend\nt\n"),
  ("upto",         "`0.upto(2)` block",
   "t = 0\n0.upto(2) do |i|\n  t = t + i\nend\nt\n"),
  ("each-arr",     "`each` over a literal array, no escape (for contrast)",
   "t = 0\n[1, 2, 3].each do |x|\n  t = t + x\nend\nt\n"),
  ("swap",         "two locals swapped through a temp inside the body",
   "a = 1\nb = 2\ni = 0\nwhile i < 3\n  t = a\n  a = b\n  b = t\n  i = i + 1\nend\na\n"),
]

def main():
    scratch = tempfile.mkdtemp(prefix="loopmore-")
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
    print(f"{'probe':14} {'validate':9} {'CRuby':12} srb")
    print("-" * 84)
    for pid, desc, rb in PROBES:
        print(f"{pid:14} {val.get(pid,'?'):9} {cruby(rb):12} {srb(rb)}")

if __name__ == "__main__":
    main()
