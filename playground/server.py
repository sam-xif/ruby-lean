#!/usr/bin/env python3
"""Ruby-in-Lean stepper playground — zero-dependency stdlib HTTP server.

Pipeline per request:  Ruby source -> export-json (desugar) -> rubycore --trace
                       -> {steps, status, detail} JSON  ->  the browser UI.

The static queries take the same first hop and a different flag: `--check` (the
nominal `infer`, whole-program), `--assn` (the open front end `inferOpen`, one
verdict per method body, in the assertion language) and `--assn-program` (L263/L264:
the open front end over the *whole* program, so a class's own `def`s cancel against
its own bodies' requirements). None of them executes anything, so none boots the
prelude and none depends on model coverage.

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


def trace(source: str, window: dict | None = None) -> dict:
    """`window` is the trace window: `{"at": SUBSTR}` or `{"from": N}`, both
    optional. Without one the trace starts at step 0, which is only useful for a
    small program — the Homebrew slice is 825,259 steps and a snapshot is ~1 KB,
    so the cap shows the first half-percent of its boot (`--trace-at`)."""
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
    argv = [str(RUBYCORE), "--trace", MAX_STEPS]
    if window:
        if window.get("at"):
            argv += ["--trace-at", str(window["at"])]
        elif window.get("from"):
            argv += ["--trace-from", str(int(window["from"]))]
    try:
        lean = subprocess.run(
            argv, input=des.stdout,
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
        if self.path not in ("/trace", "/run", "/steps", "/check", "/assn",
                             "/assn-program"):
            self._send(404, b"not found", "text/plain")
            return
        n = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(n).decode("utf-8")
        # `/trace` takes either a bare source string (as it always has) or a JSON
        # object `{"source": …, "at": …, "from": …}` carrying the window.
        source, window = body, None
        if self.path == "/trace" and body.lstrip().startswith("{"):
            try:
                req = json.loads(body)
                source, window = req.get("source", ""), req
            except ValueError:
                pass
        if self.path == "/trace":
            result = trace(source, window)
        elif self.path == "/steps":
            result = steps(source)
        elif self.path == "/check":
            result = check(source)
        elif self.path == "/assn":
            result = assn(source, top=self.headers.get("X-Assn-Top") == "1")
        elif self.path == "/assn-program":
            result = assn_program(source)
        else:
            result = run_ruby(source)
        self._send(200, json.dumps(result).encode("utf-8"), "application/json")


def steps(source: str) -> dict:
    """How many steps the program takes, with no snapshots — the number a window
    is chosen against (`rubycore --steps`)."""
    des = subprocess.run([RUBY, str(EXPORT_JSON)], input=source,
                         capture_output=True, text=True, timeout=TIMEOUT)
    if des.returncode != 0:
        return {"error": "desugar", "message": des.stderr.strip()[:500]}
    lean = subprocess.run([str(RUBYCORE), "--steps"], input=des.stdout,
                          capture_output=True, text=True, timeout=TIMEOUT)
    if lean.returncode != 0:
        return {"error": "lean", "message": lean.stderr.strip()[:500]}
    try:
        return json.loads(lean.stdout)
    except ValueError as e:
        return {"error": "lean", "message": str(e)}


def desugar(source: str) -> tuple[str | None, dict | None]:
    """Ruby source -> RubyCore JSON, or (None, error-dict). The first hop of
    every query on this server; exit 3 is the desugar's own fragment gate."""
    if not RUBYCORE.exists():
        return None, {"error": "setup",
                      "message": f"rubycore not built at {RUBYCORE} — run `cd ../lean && lake build`"}
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


def lean_query(core_json: str, *flags: str) -> dict:
    """One static `rubycore` query. Static means static: no prelude is booted and
    nothing is executed, so a non-zero exit is a real harness error rather than a
    program outcome."""
    try:
        lean = subprocess.run([str(RUBYCORE), *flags], input=core_json,
                              capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": f"rubycore {' '.join(flags)} timed out"}
    if lean.returncode != 0:
        return {"error": "lean",
                "message": lean.stderr.strip()[:500] or f"rubycore exit {lean.returncode}"}
    try:
        return json.loads(lean.stdout)
    except ValueError as e:
        return {"error": "lean", "message": f"unparseable {' '.join(flags)} output: {e}"}


def check(source: str) -> dict:
    """`infer`, whole-program (`rubycore --check`), with the Sorbet-fragment
    report beside it (`--fragment`).

    The two are **independent queries and neither causes the other**, which is
    worth stating because the pairing invites the opposite reading. A
    `missing-sig` violation is *not* why `--check` says `uncertified`: `declsOf`
    ignores the program entirely (`Types/Decls.lean`: `declsOf _p := baseDecls`),
    so `infer` never reads a `sig` and adding one to a method changes no verdict —
    a one-parameter `def` with a full `sig` is `in_fragment: true` and still
    `reject`/`uncertified`. What `infer` actually wants is a *declaration*, and
    the only rule that makes one is the `def` arm's `addRow`, which fires only for
    a zero-parameter `def` reopening a class in `reopenableClasses` at
    `top = false`. `--fragment` answers a different question — the scope a
    soundness theorem could have — and is shown because it is the other half of
    "what would it take", not because it is the cause."""
    core, err = desugar(source)
    if err:
        return err
    out = lean_query(core, "--check")
    if out.get("error"):
        return out
    frag = lean_query(core, "--fragment")
    out["fragment"] = frag
    return out


def assn(source: str, top: bool = False) -> dict:
    """`inferOpen`, per method body (`rubycore --assn`) — the assertion-language
    report of `homebrew/assertion-language.md` §11. Reports against the
    *prelude-aware* declaration table, unlike `--check`; that asymmetry is
    Main.lean's and is deliberate.

    `inferOpen` reads no `sig` either — it opens each parameter at a fresh type
    variable and reports what the body then requires — so this is already the
    sig-free view of the program. `top` adds `--assn-top`'s `Object#<main>` row,
    which is the only way to get an open verdict on a program's straight-line
    code (`bodyReports` reports `def`/`defs` only)."""
    core, err = desugar(source)
    if err:
        return err
    return lean_query(core, "--assn", *(["--assn-top"] if top else []))


def assn_program(source: str) -> dict:
    """`inferProgram`, whole-program (`rubycore --assn-program`) — L263/L264.

    The third static query, and what distinguishes it from the other two is worth
    stating because they look adjacent. Against `--check`: this accepts programs
    whose `def`s and `class`es have no declarations *yet*, and answers what the
    types would have to be rather than whether they are already known. Against
    `--assn`: the bodies share **one store**, so the requirement a `vcall` in one
    body records is cancelled by the `def` beside it — which a per-body pass
    structurally cannot do, since it hands every body a fresh store.

    An `accept` here is the **weakest** verdict the tool prints — *types under
    these class obligations* — and the JSON says so in `means`. It is also
    all-or-nothing, where `--assn` is a gradient: on a real file this reports the
    *first* construct that stopped the program, so `--assn`'s per-body census stays
    the ratchet and this is the verdict."""
    core, err = desugar(source)
    if err:
        return err
    return lean_query(core, "--assn-program")


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8077
    print(f"Ruby-in-Lean playground on http://localhost:{port}")
    print(f"  ruby:     {RUBY}")
    print(f"  rubycore: {RUBYCORE}  ({'built' if RUBYCORE.exists() else 'NOT BUILT'})")
    ThreadingHTTPServer(("127.0.0.1", port), Handler).serve_forever()


if __name__ == "__main__":
    main()
