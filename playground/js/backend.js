// The one seam between the page and whatever is executing the pipeline.
//
// Two backends answer the same nine calls:
//
//   wasm    the modules in `wasm/`, run in a worker. No server. This is what
//           GitHub Pages serves.
//   server  `server.py` on localhost, shelling out to the native binaries.
//           Kept because it is the reference: same page, same buttons, and any
//           disagreement between the two is a bug worth knowing about.
//
// Selection, in order: `?backend=wasm|server` in the URL, then `config.js`'s
// `window.PLAYGROUND_BACKEND` (which `build.sh` writes into the deployed site),
// then `server` -- because a bare checkout served by `server.py` has no built
// wasm, and guessing the other way would fail confusingly.

const params = new URLSearchParams(location.search);
export const BACKEND =
  params.get("backend") || globalThis.PLAYGROUND_BACKEND || "server";
export const WASM_BASE = globalThis.PLAYGROUND_WASM_BASE || "wasm/";

const STRIP_CHAIN = [
  "sig_strip", "visibility_strip", "freeze_strip",
  "require_strip", "const_inline", "class_sugar_strip",
];

// ---------------------------------------------------------------------------
// worker plumbing
// ---------------------------------------------------------------------------

let worker = null;
let seq = 0;
const pending = new Map();

function ensureWorker() {
  if (worker) return worker;
  worker = new Worker(new URL("./worker.js", import.meta.url), { type: "module" });
  worker.onmessage = (ev) => {
    const { id } = ev.data;
    if (id === undefined) return; // the `ready` ping
    const slot = pending.get(id);
    if (!slot) return;
    pending.delete(id);
    slot(ev.data);
  };
  return worker;
}

/** Run one module. Rejects only on infrastructure failure, not on exit != 0. */
function exec(module, args = [], stdin = "") {
  const id = ++seq;
  ensureWorker().postMessage({ id, url: `${WASM_BASE}${module}.wasm`, args, stdin });
  return new Promise((resolve, reject) => {
    pending.set(id, (d) => (d.error ? reject(new Error(d.error)) : resolve(d)));
  });
}

const json = (s, what) => {
  try { return JSON.parse(s); }
  catch (e) { throw new Error(`${what}: unparseable output — ${e.message}`); }
};

// ---------------------------------------------------------------------------
// the wasm backend
// ---------------------------------------------------------------------------

let corpusCache = null;
async function corpusData() {
  if (!corpusCache) {
    const r = await fetch("corpus.json");
    if (!r.ok) throw new Error(`corpus.json: ${r.status}`);
    corpusCache = await r.json();
  }
  return corpusCache;
}

async function stripChain(source) {
  let text = source;
  const applied = [];
  for (const stage of STRIP_CHAIN) {
    const r = await exec("ruby", [`/opt/strip/${stage}.rb`], text);
    if (r.exitCode !== 0) {
      return { error: "strip", message: `${stage}: ${r.stderr.trim().slice(0, 500)}`, applied };
    }
    text = r.stdout;
    applied.push(stage);
  }
  return { source: text, applied };
}

async function desugar(source) {
  const r = await exec("ruby", ["/opt/desugar/bin/export-json"], source);
  // The harness exits 3 for "out of the desugar fragment" -- a clean gate, not
  // a crash, and the message is the measurement.
  if (r.exitCode === 3) {
    return { error: "desugar", message: r.stderr.trim() || "out of desugar fragment" };
  }
  if (r.exitCode !== 0) {
    return { error: "desugar", message: r.stderr.trim().slice(0, 500) || "desugar failed" };
  }
  return { core: r.stdout };
}

const wasmBackend = {
  async corpus() {
    const d = await corpusData();
    return { entries: d.entries.map(({ source, sorbet, ...rest }) => rest) };
  },

  async "corpus-source"({ file }) {
    const d = await corpusData();
    const e = d.entries.find((x) => x.file === file);
    return e ? { source: e.source } : { error: "corpus", message: `no such rung: ${file}` };
  },

  async strip({ source }) {
    return stripChain(source);
  },

  async desugar({ source }) {
    const d = await desugar(source);
    if (d.error) return d;
    return { core: d.core, ast: json(d.core, "desugar").ast, bytes: d.core.length };
  },

  // Sorbet is C++ and has no wasm port. The stored verdict is accurate for a
  // rung as it sits in the corpus and false about anything else, so it is
  // offered only while the buffer still matches, and withheld the moment it
  // does not. `read_sigs.rb` reports what it read either way.
  async sorbet({ source, file }) {
    const d = await corpusData();
    const e = d.entries.find((x) => x.file === file);
    const sigs = await exec("ruby", ["/opt/deriv/read_sigs.rb"], source);
    if (sigs.exitCode !== 0) {
      return { error: "sigs", message: sigs.stderr.trim().slice(0, 500) };
    }
    const read = json(sigs.stdout, "read_sigs");
    const unmodified = e && e.source === source;
    return {
      available: Boolean(unmodified && e.sorbet),
      unmodified: Boolean(unmodified),
      srb_clean: unmodified && e.sorbet ? e.sorbet.clean : null,
      diagnostics: unmodified && e.sorbet ? e.sorbet.diagnostics : [],
      sigs: read.sigs,
      dropped: read.dropped,
      reader: "prism",
    };
  },

  async derive({ source }) {
    // Signatures come from the *annotated* source; the derivation is about the
    // stripped program. That asymmetry is the pipeline's, not this file's.
    const sigsRun = await exec("ruby", ["/opt/deriv/read_sigs.rb"], source);
    if (sigsRun.exitCode !== 0) {
      return { error: "sigs", message: sigsRun.stderr.trim().slice(0, 500) };
    }
    const sigs = json(sigsRun.stdout, "read_sigs");
    const stripped = await stripChain(source);
    if (stripped.error) return stripped;
    const des = await desugar(stripped.source);
    if (des.error) return des;
    const ast = json(des.core, "desugar");
    const emit = await exec("ruby", ["/opt/deriv/emit_deriv.rb"], JSON.stringify({ ast, sigs }));
    if (emit.exitCode !== 0) {
      return { error: "derive", message: emit.stderr.trim().slice(0, 500) };
    }
    const out = json(emit.stdout, "emit_deriv");
    return { emit: out, deriv: out.deriv, ty: out.ty, stripped: stripped.source, core: ast, sigs };
  },

  async validate({ source, deriv }) {
    const stripped = await stripChain(source);
    if (stripped.error) return stripped;
    const des = await desugar(stripped.source);
    if (des.error) return des;
    const r = await exec("validate-one", [],
      JSON.stringify({ program: json(des.core, "desugar"), deriv }));
    if (r.exitCode !== 0) {
      return { error: "validate", message: r.stderr.trim().slice(0, 500) || `exit ${r.exitCode}` };
    }
    return { ...json(r.stdout, "validateD"), ms: r.ms };
  },

  async model({ source }) {
    const des = await desugar(source);
    if (des.error) return des;
    const r = await exec("rubycore", [], des.core);
    if (r.exitCode === 3) return { error: "gate", message: r.stderr.trim().slice(0, 1000) || "model gated" };
    if (r.exitCode !== 0) return { error: "lean", message: r.stderr.trim().slice(0, 1000) || `exit ${r.exitCode}` };
    return { ...json(r.stdout, "rubycore"), ms: r.ms };
  },

  async cruby({ source }) {
    const r = await exec("ruby", [], source);
    return { stdout: r.stdout, stderr: r.stderr, returncode: r.exitCode, ms: r.ms };
  },
};

// ---------------------------------------------------------------------------
// the server backend -- the same nine calls, over `server.py`'s routes
// ---------------------------------------------------------------------------

async function post(path, body) {
  const r = await fetch(path, { method: "POST", body: JSON.stringify(body) });
  if (!r.ok) return { error: "server", message: `${path} — ${r.status} ${r.statusText}` };
  return r.json();
}

const serverBackend = {
  corpus: async () => (await fetch("/ratchet/corpus")).json(),
  "corpus-source": (b) => post("/ratchet/corpus-source", b),
  strip: (b) => post("/ratchet/strip", b),
  desugar: (b) => post("/ratchet/desugar", b),
  sorbet: async (b) => {
    const d = await post("/ratchet/sorbet", b);
    // Shape it like the wasm backend's: here Sorbet really ran.
    return d.error ? d : { ...d, available: true, unmodified: true, reader: "sorbet" };
  },
  derive: (b) => post("/ratchet/derive", b),
  validate: (b) => post("/ratchet/validate", b),
  model: (b) => post("/ratchet/model", b),
  cruby: (b) => post("/ratchet/cruby", b),
};

// ---------------------------------------------------------------------------

const impl = BACKEND === "wasm" ? wasmBackend : serverBackend;

/** The single entry point. Never throws; failures come back as `{error, message}`. */
export async function call(name, body = {}) {
  const fn = impl[name];
  if (!fn) return { error: "backend", message: `no such call: ${name}` };
  try {
    return await fn(body);
  } catch (e) {
    return { error: BACKEND, message: String((e && e.message) || e) };
  }
}

/** Warm the interpreter so the first stage press is not also a 40 MB compile. */
export function prewarm() {
  if (BACKEND !== "wasm") return;
  exec("ruby", ["/opt/deriv/read_sigs.rb"], "").catch(() => {});
}
