#!/usr/bin/env python3
"""Ruby-in-Lean stepper playground — zero-dependency stdlib HTTP server.

Pipeline per request:  Ruby source -> export-json (desugar) -> rubycore --trace
                       -> {steps, status, detail} JSON  ->  the browser UI.

The static queries take the same first hop and a different flag: `--check` (the
nominal `infer`, whole-program), `--assn` (the open front end `inferOpen`, one
verdict per method body, in the assertion language), `--assn-program` (L263/L264:
the open front end over the *whole* program, so a class's own `def`s cancel against
its own bodies' requirements), and `--check-tl` (the standalone typed-lambdas
checker, `docs/semantics/typed-lambdas-plan.md` — a *second* checker, not a flag
on `infer`, see `Types/LambdaArrow.lean`'s header for why). None of them executes
anything, so none boots the prelude and none depends on model coverage.

Run:  python3 server.py [port]      (default 8077)
Needs: CRuby 4.0.5 (brew) + a built `rubycore` (cd ../ruby-lean && lake build).
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
ROOT = HERE.parent  # ruby/
EXPORT_JSON = ROOT / "harness" / "desugar-dt" / "bin" / "export-json"
RUBYCORE = ROOT / "ruby-lean" / ".lake" / "build" / "bin" / "rubycore"
RATCHET_VALIDATE = ROOT / "ruby-lean" / ".lake" / "build" / "bin" / "validate-one"
MAX_STEPS = "4000"
# The desugar budget. It used to be 15s, which is a toy's budget: the linked
# Homebrew slice is 2,151 lines and the slice explorer feeds it to the same first
# hop. `LONG` (below) is the budget for anything that *executes* the slice.
TIMEOUT = 120


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
        return {"error": "setup", "message": f"rubycore not built at {RUBYCORE} — run `cd ../ruby-lean && lake build`"}
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
            capture_output=True, text=True, timeout=LONG,
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
        elif self.path == "/slice/files":
            self._send(200, json.dumps(slice_files()).encode(), "application/json")
        elif self.path == "/ratchet/corpus":
            self._send(200, json.dumps(ratchet_corpus()).encode(), "application/json")
        else:
            self._send(404, b"not found", "text/plain")

    # The slice-explorer routes all take a JSON object; the original routes keep
    # taking a bare source body, which is what the stepper has always sent.
    SLICE_ROUTES = {
        "/slice/source":   lambda q: slice_source(q.get("file", "")),
        "/slice/link":     lambda q: slice_link(),
        "/slice/strip":    lambda q: strip_chain(q.get("source", "")),
        "/slice/desugar":  lambda q: desugar_only(q.get("source", "")),
        "/slice/model":    lambda q: model_run(q.get("source", "")),
        "/slice/cruby":    lambda q: cruby_run(q.get("source", "")),
        "/slice/derive":   lambda q: derive(q.get("source", "")),
        "/slice/validate": lambda q: validate(q.get("source", ""), q.get("cert", "")),
        # ── Tab 3: the current typed ratchet pipeline.
        "/ratchet/strip":  lambda q: strip_chain(q.get("source", "")),
        "/ratchet/desugar": lambda q: desugar_only(q.get("source", "")),
        "/ratchet/sorbet": lambda q: ratchet_sorbet(q.get("source", "")),
        "/ratchet/derive": lambda q: ratchet_derive(q.get("source", "")),
        "/ratchet/validate": lambda q: ratchet_validate(q.get("source", ""), q.get("deriv")),
        "/ratchet/model":  lambda q: model_run(q.get("source", "")),
        "/ratchet/cruby":  lambda q: cruby_run(q.get("source", "")),
        "/ratchet/corpus-source": lambda q: ratchet_corpus_source(q.get("file", "")),
    }

    def do_POST(self):
        n = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(n).decode("utf-8")
        if self.path in self.SLICE_ROUTES:
            try:
                q = json.loads(body or "{}")
            except ValueError:
                self._send(400, b"expected JSON", "text/plain")
                return
            result = self.SLICE_ROUTES[self.path](q)
            self._send(200, json.dumps(result).encode("utf-8"), "application/json")
            return
        if self.path not in ("/trace", "/run", "/steps", "/check", "/check-tl", "/assn",
                             "/assn-program"):
            self._send(404, b"not found", "text/plain")
            return
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
        elif self.path == "/check-tl":
            result = check_tl(source)
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
                          capture_output=True, text=True, timeout=LONG)
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


def check_tl(source: str) -> dict:
    """`rubycore --check-tl` — the standalone typed-lambdas checker
    (`docs/semantics/typed-lambdas-plan.md`, `ruby-lean/RubyCore/Types/LambdaArrow.lean`).

    Deliberately a separate query from `check()`/`--check`, the way the two
    checkers are separate in the Lean tree: this one reads a `sig`-declared
    `T.proc.params(...).returns(...)` return type and checks a returned
    lambda literal against it (arity, body, pinning of captured locals),
    which `infer`/`--check` does not — `declsOf` ignores the program and no
    `def` with parameters ever gets a row there. `--check-tl`'s own fragment
    is a flat sequence of zero-arg top-level `def`s, each optionally
    sig-preceded, plus a driver — narrower than `--check`'s, on purpose."""
    core, err = desugar(source)
    if err:
        return err
    return lean_query(core, "--check-tl")


CORPUS = ROOT / "ruby-lean" / "corpus"


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


def scrub_sigs(report: dict, rb: Path) -> dict:
    """The temp path leaks into srb's diagnostics; the file the user is looking at is the
    editor, so say so rather than naming a directory that no longer exists."""
    report["diagnostics"] = [line.replace(str(rb), "(editor)")
                             for line in report.get("srb_diagnostics", [])]
    report["file"] = "(editor)"
    return report


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
            [sys.executable, str(ROOT / "ruby-lean/scripts/emit_deriv.py"),
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


# ── The Homebrew slice explorer (tab 2) ─────────────────────────────────────
# Everything here is glue over tools that already exist and are the *same* tools
# the ratchets run, never a second implementation:
#
#   file      homebrew/vendor/brew/Library/Homebrew/…      (PLAN.md §2's eight)
#   link      linker + homebrew/slice-driver/build.py      (boot stubs + driver)
#   strip     difftest/ruby/*_strip.rb                     (certify-file.sh's chain)
#   desugar   harness/desugar-dt/bin/export-json
#   model     rubycore                                     (the observation record)
#   cruby     $RUBY                                        (the oracle)
#   derive    certify/jcert.rb                             (untrusted J emitter)
#   validate  rubycore --certify-j                         (the trusted kernel Bool)
#
# The derive/validate split is deliberate and is the whole point of the pane:
# `certify-file.sh` pipes one into the other, so a failure there is one word. Here
# the certificate is a visible artifact between two buttons, and a `false` from
# `--certify-j` is a fact about *that JSON*, which you can read.

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
JCERT = ROOT / "certify" / "jcert.rb"
BUILD_SLICE = ROOT / "homebrew" / "slice-driver" / "build.py"
# The linked slice is 2,151 lines and the model runs it in 825,259 steps; 15s is
# the toy budget, not this one.
LONG = 900


def slice_files() -> dict:
    """The eight slice files, plus whether each is on disk. The vendored brew
    checkout is the only root offered: a path the browser chose would be a file
    read the server did not bound."""
    out = []
    for rel in SLICE:
        p = LIB / rel
        out.append({"file": rel, "exists": p.exists(),
                    "lines": len(p.read_text(errors="replace").splitlines()) if p.exists() else 0})
    return {"root": str(LIB), "files": out}


def slice_source(rel: str) -> dict:
    if rel not in SLICE:
        return {"error": "input", "message": f"not a slice file: {rel}"}
    p = LIB / rel
    if not p.exists():
        return {"error": "input", "message": f"missing: {p}"}
    return {"file": rel, "source": p.read_text(errors="replace")}


def slice_link() -> dict:
    """The whole slice as one program: `slice-driver/build.py` — boot stubs +
    `linker` over the three entries (which pulls all eight files, 8 spliced, 0
    thunked, 0 cycles) + `driver.rb`, the CVE-matching main.

    Two details are copied from `slice-driver/run.sh` rather than rediscovered:
    it runs under `uv` from `ruby/difftest` (the boot stubs are imported from
    `difftest/tiers/tier0/rspec_harvest.py`, whose package pulls in hypothesis),
    and the brew root is passed **realpath'd** — the linker keys its node map on
    the paths Prism reports, so a `..` in the argument is a `KeyError` three
    frames down."""
    if not BUILD_SLICE.exists():
        return {"error": "setup", "message": f"no {BUILD_SLICE}"}
    brew = os.path.realpath(str(LIB.parent.parent))
    cwd = str(ROOT / "difftest")
    argv = ([shutil.which("uv"), "run", "python"] if shutil.which("uv") else [sys.executable])
    try:
        p = subprocess.run(
            argv + [str(BUILD_SLICE), "--brew", brew, "-o", "-"],
            capture_output=True, text=True, timeout=LONG, cwd=cwd,
        )
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": "linker timed out"}
    if p.returncode != 0:
        return {"error": "linker", "message": p.stderr.strip()[-1500:] or f"exit {p.returncode}"}
    return {"source": p.stdout, "report": p.stderr.strip()}


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


def derive(source: str) -> dict:
    """`certify/jcert.rb` — the untrusted emitter. Untrusted by construction: a
    wrong certificate dies at `validateJ`'s kernel Bool, so a failure here costs
    a body we did not certify and never a false accept. `jcert.rb` raises with
    the blocking head named when the program leaves `MFrag`."""
    core, err = desugar(source)
    if err:
        return err
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".ast.json", delete=False) as f:
        f.write(core)
        astpath = f.name
    try:
        p = subprocess.run([RUBY, str(JCERT), "--ast", astpath],
                           capture_output=True, text=True, timeout=LONG)
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": "jcert timed out"}
    if p.returncode != 0:
        # `jcert.rb` raises `JCert::Blocked` naming the head it could not emit;
        # that name is the useful half of a Ruby backtrace, so it is lifted out.
        err = p.stderr.strip()
        head = err.splitlines()[0] if err else f"exit {p.returncode}"
        if ": " in head:
            head = head.split(": ", 1)[1]
        return {"error": "derive", "blocked": head, "message": err[:2000] or head}
    return {"cert": p.stdout, "core": core, "stderr": p.stderr.strip()[:2000]}


def validate(source: str, cert: str) -> dict:
    """`rubycore --certify-j` — the trusted side: one kernel `Bool`, the theorem
    `validateJ_certifies`. The certificate is whatever the box holds, which is
    the point of separating this from `derive`: an edited certificate is checked
    exactly as an emitted one is."""
    core, err = desugar(source)
    if err:
        return err
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".jcert.json", delete=False) as f:
        f.write(cert)
        certpath = f.name
    try:
        p = subprocess.run([str(RUBYCORE), "--certify-j", certpath], input=core,
                           capture_output=True, text=True, timeout=LONG)
    except subprocess.TimeoutExpired:
        return {"error": "timeout", "message": "validation timed out"}
    out = {"stdout": p.stdout, "stderr": p.stderr[:4000], "returncode": p.returncode}
    try:
        out["report"] = json.loads(p.stdout)
    except ValueError:
        pass
    return out


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8077
    print(f"Ruby-in-Lean playground on http://localhost:{port}")
    print(f"  ruby:     {RUBY}")
    print(f"  rubycore: {RUBYCORE}  ({'built' if RUBYCORE.exists() else 'NOT BUILT'})")
    print(f"  validate: {RATCHET_VALIDATE}  ({'built' if RATCHET_VALIDATE.exists() else 'NOT BUILT'})")
    ThreadingHTTPServer(("127.0.0.1", port), Handler).serve_forever()


if __name__ == "__main__":
    main()
