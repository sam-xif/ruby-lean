#!/usr/bin/env python3
"""The playground's localhost fallback: the same page, over the native binaries.

    python3 server.py [port]        # default 8077

`build.sh` produces a static site that runs everything in the browser as wasm.
This serves the identical `index.html` against `server.py` routes instead, so
the two can be compared button for button -- the page picks its backend from
`config.js` (absent here, so `server`) and `?backend=` overrides either way.

Kept for three reasons. It is the reference the wasm build is checked against;
it runs the real `srb` binary, which the browser cannot; and it needs no build
of the wasm modules, so a fresh checkout has something that works.

Needs CRuby 4.0.x on PATH (or $RUBY / brew) and a built `ruby-lean`:

    cd ../ruby-lean && lake build

Eleven routes, matching `js/backend.js`'s eleven calls exactly. The
static-query flags and the Homebrew slice explorer that used to live here are
gone; the stepper is back, because the trace is the semantics made visible.

**Restart it after editing this file.** There is no reloader.
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
EXPORT_JSON = ROOT / "desugar-dt" / "bin" / "export-json"
RUBYCORE = ROOT / "ruby-lean" / ".lake" / "build" / "bin" / "rubycore"
RATCHET_VALIDATE = ROOT / "ruby-lean" / ".lake" / "build" / "bin" / "validate-one"
CORPUS = ROOT / "ruby-lean" / "corpus"
TIMEOUT = 120
LONG = 300
STRIP_CHAIN = ["sig_strip", "visibility_strip", "freeze_strip", "require_strip",
               "const_inline", "class_sugar_strip"]

def find_ruby() -> str:
    if os.environ.get("RUBY"):
        return os.environ["RUBY"]
    try:
        prefix = subprocess.check_output(["brew", "--prefix", "ruby"], text=True).strip()
        cand = Path(prefix) / "bin" / "ruby"
        if cand.exists():
            return str(cand)
    except Exception:
        pass
    return shutil.which("ruby") or "ruby"


def trace_run(source: str, cap, at: str, frm) -> dict:
    """`rubycore --trace` — `RubyCore/Trace.lean` emits every configuration as
    JSON instead of a single observation. The window controls are not a
    nicety: a whole-program trace is only viable for a toy."""
    core, err = desugar(source)
    if err:
        return err
    argv = [str(RUBYCORE), "--trace", str(int(cap))]
    if at:
        argv += ["--trace-at", str(at)]
    elif frm:
        argv += ["--trace-from", str(int(frm))]
    try:
        lean = subprocess.run(argv, input=core, capture_output=True, text=True, timeout=LONG)
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": f"trace timed out after {LONG}s"}
    if lean.returncode != 0:
        return {"error": "lean", "message": lean.stderr.strip()[:1000] or f"exit {lean.returncode}"}
    try:
        out = json.loads(lean.stdout)
    except ValueError as e:
        return {"error": "lean", "message": f"unparseable trace: {e}"}
    try:
        out["ast"] = json.loads(core).get("ast")
    except ValueError:
        pass
    return out


def steps_run(source: str) -> dict:
    """How long is this program? The number a trace window is chosen against."""
    core, err = desugar(source)
    if err:
        return err
    try:
        lean = subprocess.run([str(RUBYCORE), "--steps"], input=core,
                              capture_output=True, text=True, timeout=LONG)
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": f"step count timed out after {LONG}s"}
    if lean.returncode != 0:
        return {"error": "lean", "message": lean.stderr.strip()[:1000] or f"exit {lean.returncode}"}
    try:
        return json.loads(lean.stdout)
    except ValueError as e:
        return {"error": "lean", "message": f"unparseable step count: {e}"}


RUBY = find_ruby()


def desugar(source: str) -> tuple[str | None, dict | None]:
    """Ruby source -> RubyCore JSON, or (None, error-dict). The first hop of
    every query on this server; exit 3 is the desugar's own fragment gate."""
    if not RUBYCORE.exists():
        return None, {"error": "setup",
                      "message": f"rubycore not built at {RUBYCORE} — run `cd ../ruby-lean && lake build`"}
    try:
        des = subprocess.run([RUBY, str(EXPORT_JSON)], input=source,
                             capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return None, {"error": "timeout", "message": "desugar timed out"}
    if des.returncode == 3:
        return None, {"error": "desugar",
                      "message": des.stderr.strip() or "out of desugar fragment"}
    if des.returncode != 0:
        return None, {"error": "desugar", "message": des.stderr.strip()[:500] or "desugar failed"}
    return des.stdout, None


def strip_chain(source: str) -> dict:
    """`certify/certify-file.sh`'s strip chain, one Ruby filter at a time so a
    failure names the transform that failed. Each transform is documented in
    `difftest/ruby/`; stripping removes traps, never meaning."""
    text = source
    applied = []
    for name in STRIP_CHAIN:
        script = ROOT / "difftest" / "ruby" / f"{name}.rb"
        try:
            p = subprocess.run([RUBY, str(script)], input=text,
                               capture_output=True, text=True, timeout=LONG)
        except subprocess.TimeoutExpired:
            return {"error": "strip", "message": f"{name} timed out", "applied": applied}
        if p.returncode != 0:
            return {"error": "strip",
                    "message": f"{name}: {p.stderr.strip()[:500] or p.returncode}",
                    "applied": applied}
        text, _ = p.stdout, applied.append(name)
    return {"source": text, "applied": applied}


def scrub_sigs(report: dict, rb: Path) -> dict:
    """The temp path leaks into srb's diagnostics; the file the user is looking at is the
    editor, so say so rather than naming a directory that no longer exists."""
    report["diagnostics"] = [line.replace(str(rb), "(editor)")
                             for line in report.get("srb_diagnostics", [])]
    report["file"] = "(editor)"
    return report


def ratchet_sorbet(source: str) -> dict:
    """`srb` over the **unstripped** program -- the annotated source as written, before
    the strip stack takes the signatures back out.

    This is `build_corpus.py`'s stage 1, run through the same `srb_sigs.py` rather than a
    second invocation of the binary, so `clean` here is the `srb_clean` a rung's
    `expect_sorbet` is recorded against. It is the one stage of the pipeline whose input is
    the top editor and not the stripped buffer: stripping is exactly the removal of what
    Sorbet reads, so running this downstream would be asking a different question."""
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        rb = Path(td) / "playground.rb"
        rb.write_text(source)
        p = subprocess.run(
            [sys.executable, str(ROOT / "ruby-lean/scripts/srb_sigs.py"), "--quiet", str(rb)],
            capture_output=True, text=True, timeout=LONG)
        if p.returncode != 0:
            return {"error": "sorbet", "message": p.stderr.strip()[:2000] or f"exit {p.returncode}"}
        try:
            report = json.loads(p.stdout)
        except ValueError as exc:
            return {"error": "sorbet", "message": f"unparseable srb_sigs output: {exc}"}
        return scrub_sigs(report, rb)


def ratchet_derive(source: str) -> dict:
    """Run the typed ladder's untrusted Sorbet -> strip -> desugar -> Deriv stages."""
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        rb = Path(td) / "playground.rb"
        rb.write_text(source)
        sigs = subprocess.run(
            [sys.executable, str(ROOT / "ruby-lean/scripts/srb_sigs.py"), "--quiet", str(rb)],
            capture_output=True, text=True, timeout=LONG)
        if sigs.returncode != 0:
            return {"error": "sorbet", "message": sigs.stderr.strip()[:2000]}
        stripped = strip_chain(source)
        if stripped.get("error"):
            return stripped
        core, err = desugar(stripped["source"])
        if err:
            return err
        sp, ap = Path(td) / "sigs.json", Path(td) / "ast.json"
        sp.write_text(sigs.stdout)
        ap.write_text(core)
        emit = subprocess.run(
            [RUBY, str(ROOT / "ruby-lean/scripts/emit_deriv.rb"),
             "--ast", str(ap), "--sigs", str(sp)],
            capture_output=True, text=True, timeout=LONG)
        if emit.returncode != 0:
            return {"error": "derive", "message": emit.stderr.strip()[:2000]}
        try:
            report = json.loads(emit.stdout)
            sig_report = json.loads(sigs.stdout)
        except ValueError as exc:
            return {"error": "derive", "message": f"unparseable pipeline output: {exc}"}
        return {"emit": report, "deriv": report.get("deriv"), "ty": report.get("ty"),
                "stripped": stripped["source"], "core": json.loads(core),
                "sorbet": scrub_sigs(sig_report, rb)}


def ratchet_validate(source: str, deriv) -> dict:
    """Check the displayed Deriv with the trusted `validateD` Bool."""
    if not RATCHET_VALIDATE.exists():
        return {"error": "setup", "message": f"validate-one not built at {RATCHET_VALIDATE} — run `cd ../ruby-lean && lake build validate-one`"}
    stripped = strip_chain(source)
    if stripped.get("error"):
        return stripped
    core, err = desugar(stripped["source"])
    if err:
        return err
    payload = {"program": json.loads(core), "deriv": deriv}
    try:
        p = subprocess.run([str(RATCHET_VALIDATE)], input=json.dumps(payload),
                           capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": "validateD timed out"}
    if p.returncode != 0:
        return {"error": "validate", "message": p.stderr.strip()[:2000] or f"exit {p.returncode}"}
    try:
        return json.loads(p.stdout)
    except ValueError as exc:
        return {"error": "validate", "message": f"unparseable validateD output: {exc}"}


# ── The Homebrew slice explorer (tab 2) ─────────────────────────────────────
# Everything here is glue over tools that already exist and are the *same* tools
# the ratchets run, never a second implementation:
#
#   file      homebrew/vendor/brew/Library/Homebrew/…      (PLAN.md §2's eight)
#   link      linker + homebrew/slice-driver/build.py      (boot stubs + driver)
#   strip     difftest/ruby/*_strip.rb                     (certify-file.sh's chain)
#   desugar   desugar-dt/bin/export-json
#   model     rubycore                                     (the observation record)
#   cruby     $RUBY                                        (the oracle)
#
# The pane's derive/validate pair is gone: it drove `certify/jcert.rb` into
# `rubycore --certify-j`, the judgment-layer certificate route, which was one of
# the pre-ratchet type-checking iterations and was removed with them. The
# certificate pipeline that is live is the ratchet's, on tab 3.

LIB = ROOT / "homebrew" / "vendor" / "brew" / "Library" / "Homebrew"
# `homebrew/fragment-gap.py`'s `SLICE`, copied rather than imported for the same
# reason `certify/certify.py` copies it (E4): two lists that are equal today and
# are allowed to stop being.
SLICE = [
    "version.rb", "version/parser.rb", "pkg_version.rb", "vulns/semver.rb",
    "vulns/cvss.rb", "vulns/purl.rb", "vulns/vulnerability.rb", "vulns/identify.rb",
]
STRIP_CHAIN = ["sig_strip", "visibility_strip", "freeze_strip", "require_strip",
               "const_inline", "class_sugar_strip"]
BUILD_SLICE = ROOT / "homebrew" / "slice-driver" / "build.py"
# The linked slice is 2,151 lines and the model runs it in 825,259 steps; 15s is
# the toy budget, not this one.
LONG = 900


def model_run(source: str) -> dict:
    """`rubycore` with no flags — the observation record the difftest compares,
    not the stepper's rendering. Long timeout: this is the whole slice."""
    core, err = desugar(source)
    if err:
        return err
    try:
        lean = subprocess.run([str(RUBYCORE)], input=core,
                              capture_output=True, text=True, timeout=LONG)
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": f"model timed out after {LONG}s"}
    if lean.returncode == 3:
        return {"error": "gate", "message": lean.stderr.strip()[:1000] or "model gated"}
    if lean.returncode != 0:
        return {"error": "lean", "message": lean.stderr.strip()[:1000] or f"exit {lean.returncode}"}
    try:
        return json.loads(lean.stdout)
    except ValueError as e:
        return {"error": "lean", "message": f"unparseable observation: {e}"}


def cruby_run(source: str) -> dict:
    """`run_ruby` with the slice's budget rather than the toy's."""
    try:
        p = subprocess.run([RUBY], input=source, capture_output=True,
                           text=True, timeout=LONG)
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": f"ruby timed out after {LONG}s"}
    return {"stdout": p.stdout, "stderr": p.stderr, "returncode": p.returncode}


def desugar_only(source: str) -> dict:
    core, err = desugar(source)
    if err:
        return err
    try:
        ast = json.loads(core).get("ast")
    except ValueError:
        ast = None
    return {"core": core, "ast": ast, "bytes": len(core)}


def corpus_stems() -> list[str]:
    """Every rung's file stem (`060-fun-recursive-factorial`), sorted the way
    `ratchet`'s own runner sorts them — filename order, which is tier order."""
    if not CORPUS.is_dir():
        return []
    return sorted(p.name.removesuffix(".meta.json") for p in CORPUS.glob("*.meta.json"))


def ratchet_corpus() -> dict:
    """The live typed ladder's `*.meta.json` records."""
    out = []
    for stem in corpus_stems():
        try:
            entry = json.loads((CORPUS / f"{stem}.meta.json").read_text())
        except ValueError:
            continue
        out.append({"file": stem, "id": entry.get("id"), "tier": entry.get("tier"),
                    "description": entry.get("description"),
                    "expect_validate": entry.get("expect_validate"),
                    "expect_sorbet": entry.get("expect_sorbet")})
    return {"root": str(CORPUS), "entries": out}


def ratchet_corpus_source(stem: str) -> dict:
    """The rung's actual Ruby (`scripts/generate_corpus.py` commits a `.rb` beside
    every `.json` — the `.json`'s `program` is that source already desugared, so this
    reads the sibling file rather than round-tripping the AST back to text)."""
    if stem not in corpus_stems():
        return {"error": "input", "message": f"not a corpus rung: {stem}"}
    p = CORPUS / f"{stem}.rb"
    if not p.exists():
        return {"error": "input", "message": f"missing: {p}"}
    return {"file": stem, "source": p.read_text(errors="replace")}


RUBY = find_ruby()

# The nine calls in `js/backend.js`. Names match; the page does not know or care
# which side of the seam it is talking to.
ROUTES = {
    "/ratchet/corpus-source": lambda q: ratchet_corpus_source(q.get("file", "")),
    "/ratchet/strip":         lambda q: strip_chain(q.get("source", "")),
    "/ratchet/desugar":       lambda q: desugar_only(q.get("source", "")),
    "/ratchet/sorbet":        lambda q: ratchet_sorbet(q.get("source", "")),
    "/ratchet/derive":        lambda q: ratchet_derive(q.get("source", "")),
    "/ratchet/validate":      lambda q: ratchet_validate(q.get("source", ""), q.get("deriv")),
    "/ratchet/model":         lambda q: model_run(q.get("source", "")),
    "/ratchet/trace":         lambda q: trace_run(q.get("source", ""), q.get("max", 400),
                                                  q.get("at", ""), q.get("from", 0)),
    "/ratchet/steps":         lambda q: steps_run(q.get("source", "")),
    "/ratchet/cruby":         lambda q: cruby_run(q.get("source", "")),
}

STATIC = {".html": "text/html; charset=utf-8", ".js": "text/javascript; charset=utf-8",
          ".json": "application/json", ".wasm": "application/wasm"}


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *_):  # quiet
        pass

    def _send(self, code: int, body: bytes, ctype: str):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path = self.path.split("?", 1)[0]
        if path in ("/", "/index.html"):
            return self._send(200, (HERE / "index.html").read_bytes(), STATIC[".html"])
        if path == "/ratchet/corpus":
            return self._send(200, json.dumps(ratchet_corpus()).encode(), STATIC[".json"])
        # `index.html` is an ES module now, so its imports have to be served
        # too. Resolved under HERE and refused if it escapes -- this is a
        # localhost dev server, but path traversal is not worth being casual about.
        rel = path.lstrip("/")
        target = (HERE / rel).resolve()
        if rel and HERE in target.parents and target.is_file() and target.suffix in STATIC:
            return self._send(200, target.read_bytes(), STATIC[target.suffix])
        self._send(404, b"not found", "text/plain")

    def do_POST(self):
        n = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(n).decode("utf-8")
        fn = ROUTES.get(self.path.split("?", 1)[0])
        if fn is None:
            return self._send(404, b"no such route", "text/plain")
        try:
            q = json.loads(body or "{}")
        except ValueError:
            return self._send(400, b"expected JSON", "text/plain")
        self._send(200, json.dumps(fn(q)).encode("utf-8"), STATIC[".json"])


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8077
    for name, p in (("rubycore", RUBYCORE), ("validate-one", RATCHET_VALIDATE)):
        if not p.exists():
            print(f"  note: {name} is not built ({p}) — `cd ../ruby-lean && lake build`")
    print(f"playground on http://localhost:{port}   (ruby: {RUBY})")
    ThreadingHTTPServer(("127.0.0.1", port), Handler).serve_forever()


if __name__ == "__main__":
    main()
