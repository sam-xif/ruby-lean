import json, os, subprocess, sys
HARNESS = "harness/desugar-dt/bin/export-json"
OUT = "/tmp/probes"
for f in os.listdir(OUT):
    os.remove(os.path.join(OUT, f))

PROBES = [
 # A -- behavioural fidelity of the Symbol#to_proc arm
 ("a1-call",        ':upcase.to_proc.call("ab")\n'),
 ("a2-blockpass",   '[1, 2, 3].map(&:to_s)\n'),
 ("a3-extra-args",  ':+.to_proc.call(1, 2)\n'),
 ("a4-lambdap",     'p = :upcase.to_proc\np.lambda?\n'),
 ("a5-arity",       'p = :upcase.to_proc\np.arity\n'),
 ("a6-class",       ':upcase.to_proc.class.to_s\n'),
 ("a7-zero-args",   'p = :upcase.to_proc\np.call\n'),
 ("a8-no-method",   ':no_such_method_zz.to_proc.call(1)\n'),
 # B -- is the model's `captured := 0` observable through the body's free names?
 ("b1-shadow-recv", '__recv = "zzz"\n:upcase.to_proc.call("ab")\n'),
 ("b2-shadow-rest", '__rest = "zzz"\n:+.to_proc.call(1, 2)\n'),
 ("b3-in-method",   'def f\n  :upcase.to_proc.call("ab")\nend\nf\n'),
 ("b4-made-in-m",   'def mk\n  y = 99\n  :upcase.to_proc\nend\np = mk\np.call("ab")\n'),
 ("b5-no-write",    'x = 1\np = :to_s.to_proc\np.call(2)\nx\n'),
 # C -- the hazard the seal exists for, and whether to_proc is an instance of it
 ("c1-real-hazard", 'x = 1\nf = lambda { x = 2 }\ndef g(p)\n  p.call\nend\ng(f)\nx\n'),
 ("c2-toproc-inert",'x = 1\np = :to_s.to_proc\ndef g(q)\n  q.call(5)\nend\ng(p)\nx\n'),
 ("c3-inside-meth", 'def outer\n  z = 1\n  [1].map(&:to_s)\n  z\nend\nouter\n'),
 # D -- places the arm could plausibly diverge
 ("d1-identity",    'a = :upcase.to_proc\nb = :upcase.to_proc\na.equal?(b)\n'),
 ("d2-frozen",      ':upcase.to_proc.frozen?\n'),
 ("d3-reuse",       'p = :upcase.to_proc\n[p.call("a"), p.call("b")]\n'),
 ("d4-nested",      '[[1], [2]].map(&:first).map(&:to_s)\n'),
]

for i, (pid, src) in enumerate(PROBES, start=1):
    base = f"{i:03d}-{pid}"
    with open(os.path.join(OUT, base + ".rb"), "w") as f:
        f.write(src)
    prog = subprocess.run([HARNESS, os.path.join(OUT, base + ".rb")],
                          capture_output=True, text=True)
    if prog.returncode != 0:
        print("DESUGAR FAIL", base, prog.stderr[:200]); continue
    entry = {"id": pid, "tier": 9, "description": "seal-fidelity probe",
             "program": json.loads(prog.stdout),
             "expect_validate": False, "false_reason": "unsafe_program"}
    with open(os.path.join(OUT, base + ".json"), "w") as f:
        json.dump(entry, f, indent=2); f.write("\n")
print("wrote", len(PROBES), "probes")
