#!/usr/bin/env python3
"""Three-way probe of `while`-loop strictness: `validate` vs CRuby vs Sorbet.

Answers "how strict is `Judge.while'`, and are ordinary imperative loop patterns
allowed?" by measurement rather than by reading the premises. For each snippet:

  * **CRuby**  -- ground truth: does it raise a type-stuck error (NoMethodError /
                 ArgumentError / TypeError) or not?
  * **validate** -- the ratchet's own checker, via a scratch corpus and `.lake/build/bin/ratchet`.
  * **srb**    -- `sorbet` at `# typed: true`, for comparison.

Run from `ratchet/`:  python3 probes/loop_strictness.py
"""
import glob, json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
RAT = os.path.normpath(os.path.join(HERE, ".."))
EXPORT = os.path.normpath(os.path.join(RAT, "..", "harness", "desugar-dt", "bin", "export-json"))

def find_sorbet():
    if os.environ.get("SORBET"):
        return os.environ["SORBET"]
    for pat in ["/opt/homebrew/lib/ruby/gems/*/gems/sorbet-static-*/libexec/sorbet",
                os.path.expanduser("~/.gem/ruby/*/gems/sorbet-static-*/libexec/sorbet")]:
        hits = sorted(glob.glob(pat))
        if hits:
            return hits[-1]
    return "srb"
SORBET = find_sorbet()

# (id, description, ruby)
PROBES = [
  # --- counters, the user's question ---------------------------------------
  ("inc",        "increment counter (corpus 184's shape)",
   "i = 0\nwhile i < 3\n  i = i + 1\nend\ni\n"),
  ("dec",        "DECREMENTING counter",
   "i = 3\nwhile i > 0\n  i = i - 1\nend\ni\n"),
  ("dec-opassign", "decrement via `i -= 1`",
   "i = 3\nwhile i > 0\n  i -= 1\nend\ni\n"),
  ("dec-by-2",   "decrement by 2",
   "i = 10\nwhile i > 0\n  i = i - 2\nend\ni\n"),
  ("accum",      "accumulate into a second local",
   "i = 0\nn = 0\nwhile i < 3\n  n = n + i\n  i = i + 1\nend\nn\n"),
  ("accum-str",  "accumulate a String",
   "i = 0\ns = \"\"\nwhile i < 3\n  s = s + \"a\"\n  i = i + 1\nend\ns\n"),
  ("accum-float", "float counter",
   "x = 0.0\nwhile x < 1.0\n  x = x + 0.5\nend\nx\n"),
  ("until-dec",  "`until` with a decrement",
   "i = 3\nuntil i <= 0\n  i = i - 1\nend\ni\n"),
  ("nested",     "nested while loops",
   "i = 0\nt = 0\nwhile i < 3\n  j = 0\n  while j < 3\n    t = t + 1\n    j = j + 1\n  end\n  i = i + 1\nend\nt\n"),
  ("loop-value", "the loop as a statement, value discarded",
   "i = 0\nwhile i < 3\n  i = i + 1\nend\n1\n"),
  ("while-nil",  "the while expression's own value",
   "i = 0\nx = while i < 3\n  i = i + 1\nend\nx\n"),
  # --- escapes -------------------------------------------------------------
  ("break-inf",  "break out of `while true` (the canonical imperative loop)",
   "i = 0\nwhile true\n  i = i + 1\n  break if i > 3\nend\ni\n"),
  ("break-plain","break with no assignment before it",
   "i = 0\nwhile i < 10\n  break if i == 0\n  i = i + 1\nend\ni\n"),
  ("next-after-inc", "`next` AFTER the increment (the only terminating placement)",
   "i = 0\nn = 0\nwhile i < 4\n  i = i + 1\n  next if i == 2\n  n = n + i\nend\nn\n"),
  ("next-before-inc", "`next` before any assignment (nxtPrefixOk's shape; diverges)",
   "i = 0\nwhile i < 4\n  next if false\n  i = i + 1\nend\ni\n"),
  ("each-next",  "`next` in an each block, for contrast (corpus 186)",
   "s = 0\n[1, 2, 3, 4].each do |x|\n  next if x == 2\n  s = s + x\nend\ns\n"),
  # --- type-changing bodies ------------------------------------------------
  ("widen-nil",  "SAFE but widening: x starts nil, becomes Integer in the body",
   "x = nil\ni = 0\nwhile i < 3\n  x = i\n  i = i + 1\nend\ni\n"),
  ("widen-nil-use", "…and then used",
   "x = nil\ni = 0\nwhile i < 3\n  x = i\n  i = i + 1\nend\nx.nil?\n"),
  ("retype-unsafe", "UNSAFE: body retypes x, used as Integer after",
   "x = 0\ni = 0\nwhile i < 1\n  x = \"s\"\n  i = i + 1\nend\nx + 1\n"),
  ("retype-restore", "SAFE: body retypes x but restores it before the end",
   "x = 0\ni = 0\nwhile i < 1\n  x = \"s\"\n  x = 2\n  i = i + 1\nend\nx + 1\n"),
  ("new-local",  "a local first assigned inside the body, used after",
   "i = 0\nwhile i < 3\n  y = i\n  i = i + 1\nend\ni\n"),
  # --- mutation rather than reassignment ----------------------------------
  ("push",       "mutate an array rather than rebinding",
   "a = []\ni = 0\nwhile i < 3\n  a.push(i)\n  i = i + 1\nend\na.length\n"),
  ("arr-concat", "rebind an array by concatenation",
   "a = []\ni = 0\nwhile i < 3\n  a = a + [i]\n  i = i + 1\nend\na.length\n"),
  # --- divergence ---------------------------------------------------------
  ("while-true", "`while true; end` -- diverges; safe by prefix-closure",
   "while true\nend\n"),
]

def cruby(rb):
    with tempfile.NamedTemporaryFile("w", suffix=".rb", delete=False) as f:
        f.write(rb); p = f.name
    try:
        r = subprocess.run(["ruby", p], capture_output=True, text=True, timeout=5)
    except subprocess.TimeoutExpired:
        os.unlink(p); return "diverges"
    os.unlink(p)
    if r.returncode == 0:
        return "ok"
    err = r.stderr
    for fam in ("NoMethodError", "ArgumentError", "TypeError"):
        if fam in err:
            return "STUCK:" + fam
    return "raise:" + err.strip().split("\n")[-1][:40]

def srb(rb):
    d = tempfile.mkdtemp()
    p = os.path.join(d, "probe.rb")
    open(p, "w").write("# typed: true\n" + rb)
    r = subprocess.run([SORBET, "--no-config", "--silence-dev-message", p],
                       capture_output=True, text=True)
    if r.returncode == 0:
        return "ok"
    msgs = []
    for line in (r.stdout + r.stderr).split("\n"):
        if line.startswith(p + ":") and "https://srb.help/" in line:
            body = line.split(":", 2)[2].strip()
            msg, _, url = body.rpartition("https://srb.help/")
            msgs.append(f"{url} {msg.strip()[:52]}")
    return "; ".join(msgs[:2]) if msgs else "ERR(unparsed)"

def main():
    scratch = tempfile.mkdtemp(prefix="loopprobe-")
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
            pid = line.split()[2].rstrip(":")
            val[pid] = "true" if "validate=true" in line else "false"

    print(f"{'probe':18} {'validate':9} {'CRuby':22} srb")
    print("-" * 96)
    for pid, desc, rb in PROBES:
        print(f"{pid:18} {val.get(pid,'?'):9} {cruby(rb):22} {srb(rb)}")
    print()
    print("sorbet:", SORBET)
    print("scratch:", scratch)

if __name__ == "__main__":
    main()
