#!/usr/bin/env python3
"""Ruby-in-Lean stepper playground — zero-dependency stdlib HTTP server.

Pipeline per request:  Ruby source -> export-json (desugar) -> rubycore --trace
                       -> {steps, status, detail} JSON  ->  the browser UI.

Run:  python3 server.py [port]      (default 8077)
Needs: CRuby 4.0.5 (brew) + a built `rubycore` (cd ../lean && lake build).
"""
import json
import os
import shutil
import subprocess
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent  # ruby/
EXPORT_JSON = ROOT / "harness" / "desugar-dt" / "bin" / "export-json"
RUBYCORE = ROOT / "lean" / ".lake" / "build" / "bin" / "rubycore"
MAX_STEPS = "4000"
TIMEOUT = 15


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


RUBY = find_ruby()


def trace(source: str) -> dict:
    if not RUBYCORE.exists():
        return {"error": "setup", "message": f"rubycore not built at {RUBYCORE} — run `cd ../lean && lake build`"}
    try:
        des = subprocess.run(
            [RUBY, str(EXPORT_JSON)], input=source,
            capture_output=True, text=True, timeout=TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": "desugar timed out"}
    if des.returncode == 3:
        return {"error": "desugar", "message": des.stderr.strip() or "out of desugar fragment"}
    if des.returncode != 0:
        return {"error": "desugar", "message": des.stderr.strip()[:500] or "desugar failed"}
    # Desugar succeeded — keep the RubyCore AST for the s-expression pane, and
    # attach it to every downstream outcome (even a Lean gate) so it stays
    # visible whenever the program made it past the desugar.
    ast = None
    try:
        ast = json.loads(des.stdout).get("ast")
    except ValueError:
        pass
    try:
        lean = subprocess.run(
            [str(RUBYCORE), "--trace", MAX_STEPS], input=des.stdout,
            capture_output=True, text=True, timeout=TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": "stepper timed out", "ast": ast}
    if lean.returncode != 0:
        return {"error": "lean", "message": lean.stderr.strip()[:500] or f"rubycore exit {lean.returncode}", "ast": ast}
    try:
        result = json.loads(lean.stdout)
    except ValueError as e:
        return {"error": "lean", "message": f"unparseable trace: {e}", "ast": ast}
    result["ast"] = ast
    return result


def run_ruby(source: str) -> dict:
    """Execute the source in real CRuby and capture stdout/stderr."""
    try:
        p = subprocess.run(
            [RUBY], input=source, capture_output=True, text=True, timeout=TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": f"ruby timed out after {TIMEOUT}s"}
    return {"stdout": p.stdout, "stderr": p.stderr, "returncode": p.returncode}


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
        if self.path in ("/", "/index.html"):
            self._send(200, (HERE / "index.html").read_bytes(), "text/html; charset=utf-8")
        else:
            self._send(404, b"not found", "text/plain")

    def do_POST(self):
        if self.path not in ("/trace", "/run"):
            self._send(404, b"not found", "text/plain")
            return
        n = int(self.headers.get("Content-Length", 0))
        source = self.rfile.read(n).decode("utf-8")
        result = trace(source) if self.path == "/trace" else run_ruby(source)
        self._send(200, json.dumps(result).encode("utf-8"), "application/json")


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8077
    print(f"Ruby-in-Lean playground on http://localhost:{port}")
    print(f"  ruby:     {RUBY}")
    print(f"  rubycore: {RUBYCORE}  ({'built' if RUBYCORE.exists() else 'NOT BUILT'})")
    ThreadingHTTPServer(("127.0.0.1", port), Handler).serve_forever()


if __name__ == "__main__":
    main()
