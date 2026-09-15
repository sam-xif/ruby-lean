#!/usr/bin/env python3
"""build_corpus.py -- every rung through the four untrusted stages, into `build/`.

    scripts/build_corpus.py [--jobs N] [--only 001,014] [corpus-dir]

For each `corpus/NNN-id.rb` (Sorbet-annotated) and its `NNN-id.meta.json`:

  1. `srb` over the **annotated** source  -> the signature manifest, and srb's own verdict
  2. the strip stack (`sig_strip` first)  -> the plain program
  3. `export-json` over the stripped one  -> the AST the certificate is about
  4. `emit_deriv.py`                      -> a `Deriv`, or a named block

and writes one `build/NNN-id.rung.json` carrying all of it. Stage 5 -- the only trusted
one -- is `lake exe ratchetd`, which reads these files and nothing else.

Everything in `build/` is derived and disposable; the `.rb` is the source of truth.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)                 # ruby-lean/
RUBY = os.path.dirname(ROOT)                 # ruby/
STRIPS = [os.path.join(RUBY, "difftest", "ruby", s) for s in
          ("sig_strip.rb", "visibility_strip.rb", "freeze_strip.rb",
           "require_strip.rb", "const_inline.rb", "class_sugar_strip.rb")]
EXPORT = os.path.join(RUBY, "harness", "desugar-dt", "bin", "export-json")


def strip(src: str) -> str:
    """The strip stack, `certify/certify-file.sh`'s, `sig_strip` first."""
    cur = src
    for s in STRIPS:
        p = subprocess.run(["ruby", s], input=cur, capture_output=True, text=True)
        if p.returncode != 0:
            raise RuntimeError(f"{os.path.basename(s)}: {p.stderr.strip()}")
        cur = p.stdout
    return cur


def build(base: str, corpus: str, outdir: str) -> dict:
    rb = os.path.join(corpus, base + ".rb")
    with open(os.path.join(corpus, base + ".meta.json")) as fh:
        meta = json.load(fh)
    rec = dict(meta)
    rec["base"] = base

    # 1. Sorbet, over the annotated source.
    p = subprocess.run([sys.executable, os.path.join(HERE, "srb_sigs.py"), "--quiet", rb],
                       capture_output=True, text=True)
    if p.returncode != 0:
        rec["stage"] = "sorbet"
        rec["error"] = p.stderr.strip()[:400]
        return rec
    sigs = json.loads(p.stdout)
    rec["srb_clean"] = sigs["srb_clean"]
    rec["srb_diagnostics"] = sigs["srb_diagnostics"]
    rec["sigs"] = len(sigs["sigs"])
    rec["dropped"] = sigs["dropped"]

    # 2-3. The stripped program and its AST.
    try:
        with open(rb) as fh:
            stripped = strip(fh.read())
        with open(os.path.join(outdir, base + ".stripped.rb"), "w") as fh:
            fh.write(stripped)
        e = subprocess.run([EXPORT, os.path.join(outdir, base + ".stripped.rb")],
                           capture_output=True, text=True)
        if e.returncode != 0:
            rec["stage"] = "export"
            rec["error"] = e.stderr.strip()[:400]
            return rec
        rec["program"] = json.loads(e.stdout)
    except Exception as exc:                      # noqa: BLE001 -- reported, not raised
        rec["stage"] = "strip"
        rec["error"] = str(exc)[:400]
        return rec

    # 4. The emitter.
    sp = os.path.join(outdir, base + ".sigs.json")
    ap = os.path.join(outdir, base + ".ast.json")
    with open(sp, "w") as fh:
        json.dump(sigs, fh, indent=1)
    with open(ap, "w") as fh:
        json.dump(rec["program"], fh)
    d = subprocess.run([sys.executable, os.path.join(HERE, "emit_deriv.py"),
                        "--ast", ap, "--sigs", sp], capture_output=True, text=True)
    if d.returncode != 0:
        rec["stage"] = "emit"
        rec["error"] = d.stderr.strip()[:400]
        return rec
    rec["emit"] = json.loads(d.stdout)
    rec["stage"] = "done"
    return rec


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("corpus", nargs="?", default=os.path.join(ROOT, "corpus"))
    ap.add_argument("--out", default=os.path.join(ROOT, "build"))
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--only", help="comma-separated prefixes, e.g. 001,014")
    args = ap.parse_args(argv)

    os.makedirs(args.out, exist_ok=True)
    bases = sorted(f[:-len(".meta.json")] for f in os.listdir(args.corpus)
                   if f.endswith(".meta.json"))
    if args.only:
        pfx = tuple(args.only.split(","))
        bases = [b for b in bases if b.startswith(pfx)]
    if not bases:
        print(f"no rungs under {args.corpus}", file=sys.stderr)
        return 1

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        recs = list(ex.map(lambda b: build(b, args.corpus, args.out), bases))

    for rec in recs:
        with open(os.path.join(args.out, rec["base"] + ".rung.json"), "w") as fh:
            json.dump(rec, fh, indent=1)

    done = sum(1 for r in recs if r.get("stage") == "done")
    emitted = sum(1 for r in recs if r.get("emit", {}).get("status") == "ok")
    clean = sum(1 for r in recs if r.get("srb_clean"))
    print(f"built {len(recs)} rungs -> {args.out}")
    print(f"  srb clean:        {clean}/{len(recs)}")
    print(f"  pipeline reached the emitter: {done}/{len(recs)}")
    print(f"  derivation emitted:           {emitted}/{len(recs)}")
    for r in recs:
        if r.get("stage") not in ("done",):
            print(f"  !! {r['base']}: stage {r.get('stage')}: {r.get('error','')[:120]}",
                  file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
