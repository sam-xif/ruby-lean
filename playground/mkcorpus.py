#!/usr/bin/env python3
"""Bake the corpus into one JSON file for the static build.

    mkcorpus.py <out.json>

`server.py` serves the rungs from disk, one fetch per rung plus one for the
index. A static page cannot shell out to find them, and 259 round trips to open
a dropdown is not a page -- so the whole corpus goes into a single file: each
rung's metadata, its annotated source, and the Sorbet verdict recorded for it.

**The stored verdict is only true of the rung as it sits in the corpus.** It is
carried here so the page can show it while the buffer matches, and the page is
responsible for dropping it the moment the user edits -- see `backend.js`'s
`sorbet` call, which compares the buffer against `source` before offering it.
Sorbet itself cannot run in the browser; `read_sigs.rb` supplies the signatures
and says `"verdict": "not-checked"`.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PKG = HERE.parent / "ruby-lean"
CORPUS = PKG / "corpus"
BUILD = PKG / "build"


def main(out: Path) -> int:
    if not CORPUS.is_dir():
        sys.exit(f"no corpus at {CORPUS}")

    entries = []
    missing_sigs = 0
    # Filename order is tier order, which is the order the ratchet's own runner
    # uses; the dropdown should read the same way the gate does.
    for meta_path in sorted(CORPUS.glob("*.meta.json")):
        stem = meta_path.name.removesuffix(".meta.json")
        rb = CORPUS / f"{stem}.rb"
        if not rb.exists():
            continue
        try:
            meta = json.loads(meta_path.read_text())
        except ValueError:
            continue

        sorbet = None
        sigs_path = BUILD / f"{stem}.sigs.json"
        if sigs_path.exists():
            try:
                s = json.loads(sigs_path.read_text())
                sorbet = {"clean": s.get("srb_clean"),
                          "diagnostics": s.get("srb_diagnostics", [])}
            except ValueError:
                pass
        if sorbet is None:
            missing_sigs += 1

        entries.append({
            "file": stem,
            "id": meta.get("id"),
            "tier": meta.get("tier"),
            "description": meta.get("description"),
            "expect_validate": meta.get("expect_validate"),
            "expect_sorbet": meta.get("expect_sorbet"),
            "source": rb.read_text(),
            "sorbet": sorbet,
        })

    out.write_text(json.dumps({"entries": entries}, separators=(",", ":")))
    kb = out.stat().st_size / 1024
    print(f"    {out.name}  {len(entries)} rungs, {kb:.0f} KB"
          + (f"  ({missing_sigs} with no recorded Sorbet verdict)" if missing_sigs else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(Path(sys.argv[1] if len(sys.argv) > 1 else "corpus.json")))
