// Drive the built site's JavaScript headlessly, against the real wasm modules.
//
//   playground/build.sh && node --experimental-wasm-exnref playground/check.mjs
//
// (The flag is node's; browsers need nothing. It enables the standard wasm
// exception encoding -- `exnref`/`try_table` -- which the Lean modules are
// compiled with and which Chrome, Firefox and Safari have shipped.)
//
// This imports the *actual* `backend.js`, `worker.js` and `wasi.js` out of
// `dist/` and runs all eleven calls against the real modules. It is not a mock of
// the pipeline; the only things stubbed are the four browser globals the code
// touches.
//
// ## Those stubs model base-URL resolution on purpose
//
// The first version of this file resolved every fetch by string-munging the
// path, and so could not see that `backend.js` was handing the worker a
// *relative* wasm URL. A worker resolves relative URLs against its own script
// URL, so `wasm/ruby.wasm` posted from `js/worker.js` becomes
// `js/wasm/ruby.wasm` and 404s -- in the browser only. The harness was green
// and the page was broken.
//
// So: `fetch` resolves through `new URL(u, base)` and refuses anything outside
// `dist/`, and the fake `Worker` checks each posted URL the way the real worker
// would see it. Keep both if you touch this.
//
// ## What it does not cover
//
// Rendering. Nothing here constructs a DOM, so `index.html`'s own script -- the
// stage rail, the verdict box, the step view -- is unexercised. A green
// run means the pipeline and its plumbing work, not that the page looks right.

import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";

const HERE = path.dirname(new URL(import.meta.url).pathname);
const DIST = path.join(HERE, "dist");
if (!fs.existsSync(path.join(DIST, "index.html"))) {
  console.error(`no ${DIST} — run playground/build.sh first`);
  process.exit(1);
}

const DOC = pathToFileURL(path.join(DIST, "index.html")).href;
globalThis.location = { href: DOC, search: "?backend=wasm" };
globalThis.document = { baseURI: DOC };

globalThis.fetch = async (url, _opts, base = DOC) => {
  const p = new URL(String(url), base).pathname;
  if (!p.startsWith(DIST + "/")) throw new Error(`fetch escaped dist: ${p}`);
  if (!fs.existsSync(p)) {
    return { ok: false, status: 404, statusText: `not found: ${p.slice(DIST.length + 1)}` };
  }
  return new Response(fs.readFileSync(p), {
    headers: { "content-type": p.endsWith(".wasm") ? "application/wasm" : "application/json" },
  });
};

// A Worker that is really this thread: import worker.js against a fake `self`.
let workerBase = null;
globalThis.Worker = class {
  constructor(url) {
    this.onmessage = null;
    const inbox = { postMessage: (d) => queueMicrotask(() => this.onmessage?.({ data: d })) };
    workerBase = String(url);
    this._ready = (async () => {
      globalThis.self = inbox;
      await import(workerBase);
      this._inner = globalThis.self;
    })();
  }
  async postMessage(d) {
    await this._ready;
    if (d.url) {
      // What the real worker would resolve this to.
      const seen = new URL(d.url, workerBase);
      if (!fs.existsSync(seen.pathname)) {
        const fromDoc = new URL(d.url, DOC);
        throw new Error(
          `worker would fetch ${seen.pathname} — does not exist` +
          (fs.existsSync(fromDoc.pathname)
            ? `\n  the file is at ${fromDoc.pathname}; the URL must be absolute`
            : ""));
      }
    }
    this._inner.onmessage({ data: d });
  }
};

const { call } = await import(pathToFileURL(path.join(DIST, "js/backend.js")).href);

let failures = 0;
const ok = (name, cond, detail = "") => {
  if (!cond) failures++;
  console.log(`  ${cond ? "ok  " : "FAIL"}  ${name}${detail ? "  " + detail : ""}`);
};

const RUNG = process.argv[2] || "063-class-two-getters";

console.log(`checking dist/ against the real modules (rung: ${RUNG})`);

const corpus = await call("corpus");
ok("corpus", Array.isArray(corpus.entries) && corpus.entries.length > 0,
   `${corpus.entries?.length} rungs`);

const got = await call("corpus-source", { file: RUNG });
ok("corpus-source", typeof got.source === "string" && got.source.length > 0);
const src = got.source;

const sigs = await call("sorbet", { source: src, file: RUNG });
ok("signatures", Array.isArray(sigs.sigs), `${sigs.sigs?.length} read by ${sigs.reader}`);
ok("verdict offered while unmodified", sigs.unmodified === true);

const st = await call("strip", { source: src });
ok("strip", st.applied?.length === 6, `${st.source?.split("\n").length} lines out`);

const des = await call("desugar", { source: st.source });
ok("desugar", typeof des.bytes === "number" && des.ast, `${des.bytes} bytes`);

const der = await call("derive", { source: src });
ok("derive", Boolean(der.deriv), der.deriv ? `ty=${JSON.stringify(der.ty)}` : der.emit?.why);

if (der.deriv) {
  const v = await call("validate", { source: src, deriv: der.deriv });
  ok("validateD", v.validateD === true, `${v.ms} ms`);
}

const model = await call("model", { source: st.source });
const cruby = await call("cruby", { source: st.source });
ok("model", !model.error, `result ${model.result_repr}`);
ok("cruby", !cruby.error, `exit ${cruby.returncode}`);
ok("model and oracle agree on stdout", (model.stdout ?? null) === (cruby.stdout ?? null));

// The stepper: `RubyCore/Trace.lean` emitting every configuration, which is the
// same `stepFn` the differential tests run against CRuby.
const steps = await call("steps", { source: st.source });
ok("step count", typeof steps.steps === "number", `${steps.steps} steps, ${steps.status}`);

const tr = await call("trace", { source: st.source, max: 400 });
ok("trace", Array.isArray(tr.steps) && tr.steps.length > 0, `${tr.steps?.length} snapshots`);
const snap = tr.steps?.[0] ?? {};
ok("snapshot shape",
   typeof snap.ctl === "string" && Array.isArray(snap.frames) && Array.isArray(snap.konts),
   `ctl=${JSON.stringify(snap.ctl)}`);
ok("frames carry locals and self",
   snap.frames.length > 0 && "self" in snap.frames[0] && "locals" in snap.frames[0]);

// The window controls, which are what make a trace usable on anything real.
const win = await call("trace", { source: st.source, max: 3, from: 10 });
ok("--trace-from", win.first_step === 10, `first_step=${win.first_step}`);
const atRun = await call("trace", { source: st.source, max: 3, at: "send ." });
ok("--trace-at", (atRun.steps?.[0]?.ctl || "").includes("send ."),
   `first_step=${atRun.first_step} ctl=${JSON.stringify(atRun.steps?.[0]?.ctl)}`);

// The obligation from the Sorbet substitution: a recorded verdict is true of the
// rung as stored and of nothing else, so an edit must withdraw it.
const edited = src + "\n# an edit the corpus knows nothing about\n";
const s2 = await call("sorbet", { source: edited, file: RUNG });
ok("verdict withheld after an edit", s2.available === false && s2.unmodified === false);
ok("signatures still read after an edit", (s2.sigs || []).length === (sigs.sigs || []).length);

console.log(failures ? `\n${failures} failure(s)` : "\nall checks passed");
process.exit(failures ? 1 : 0);
