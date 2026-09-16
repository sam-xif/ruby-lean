#!/usr/bin/env python3
"""Does reading signatures off the source agree with reading them out of Sorbet?

    scripts/cmp_sig_readers.py

Compares two ways of getting to a `Deriv`, over every rung in `build/`:

    reference   srb_sigs.py's stored sigs.json  ->  emit_deriv.rb
    candidate   read_sigs.rb (Prism, no Sorbet) ->  emit_deriv.rb

Same emitter both sides, so the only variable is where the signatures came
from. That is the question this is asking.

and judges them where it matters -- by what `validateD` says about the
derivation each produces, not by whether the two emitters printed the same
bytes. A weaker reader is allowed to block earlier or propose something the
checker then rejects (`Ratchet/Deriv.lean`: every declared type is re-derived,
so a wrong signature costs a failed certification, never a wrong accept). What
it may not do is change which rungs are **accepted**.

That is the number to watch: `rungs accepted` must match, and must be the
`fragment N` the typed ratchet reports.
"""
import json, subprocess, sys, glob, os
V = "./.lake/build/bin/validate-one"
def verdict(deriv_json, ast):
    d = json.loads(deriv_json)
    if d["status"] != "ok": return "blocked"
    p = subprocess.run([V], input=json.dumps({"program": ast, "deriv": d["deriv"]}),
                       capture_output=True, text=True)
    if p.returncode != 0: return "validate-error"
    return "accept" if json.loads(p.stdout)["validateD"] else "reject"

same = diff = 0; rows = []; acc_ref = acc_cand = 0
for astf in sorted(glob.glob("build/*.ast.json")):
    stem = os.path.basename(astf)[:-len(".ast.json")]
    sigs_f, rb = f"build/{stem}.sigs.json", f"corpus/{stem}.rb"
    if not (os.path.exists(sigs_f) and os.path.exists(rb)): continue
    ast = json.load(open(astf))
    ref = subprocess.run(["ruby", "scripts/emit_deriv.rb", "--ast", astf,
        "--sigs", sigs_f], capture_output=True, text=True).stdout
    rs = subprocess.run(["ruby", "scripts/read_sigs.rb"], stdin=open(rb),
        capture_output=True, text=True).stdout
    cand = subprocess.run(["ruby", "scripts/emit_deriv.rb"],
        input=json.dumps({"ast": ast, "sigs": json.loads(rs)}),
        capture_output=True, text=True).stdout
    a, b = verdict(ref, ast), verdict(cand, ast)
    acc_ref += a == "accept"; acc_cand += b == "accept"
    if a == b: same += 1
    else:
        diff += 1; rows.append((stem, a, b))
print(f"validateD verdict: {same} identical, {diff} differ")
print(f"  rungs accepted, Sorbet path: {acc_ref}")
print(f"  rungs accepted, Prism path:  {acc_cand}")
for r in rows: print(f"  !! {r[0]}: sorbet={r[1]} prism={r[2]}")
