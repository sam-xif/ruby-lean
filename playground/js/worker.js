// Runs the wasm modules off the main thread.
//
// Not an optimisation. A `rubycore` run or a cold `ruby.wasm` start is hundreds
// of milliseconds to several seconds of synchronous work inside the module, and
// on the main thread that is a frozen tab with no way to show that anything is
// happening. Here the page stays live and can say "running".
//
// Compiled modules are cached per URL, so the ~4 s first `ruby.wasm` compile is
// paid once per tab rather than once per stage.

import { run } from "./wasi.js";

const compiled = new Map();

function moduleFor(url) {
  if (!compiled.has(url)) {
    const p = typeof WebAssembly.compileStreaming === "function"
      ? WebAssembly.compileStreaming(fetch(url))
      : fetch(url).then((r) => r.arrayBuffer()).then((b) => WebAssembly.compile(b));
    // A failed compile must not poison the cache: drop it so a retry can work.
    compiled.set(url, p.catch((e) => { compiled.delete(url); throw e; }));
  }
  return compiled.get(url);
}

self.onmessage = async (ev) => {
  const { id, url, args = [], stdin = "" } = ev.data;
  const t0 = performance.now();
  try {
    const mod = await moduleFor(url);
    const out = await run(mod, { args, stdin });
    self.postMessage({ id, ...out, ms: Math.round(performance.now() - t0) });
  } catch (e) {
    self.postMessage({ id, error: String((e && e.message) || e) });
  }
};

// Let the page know a module is warm, so it can drop a "loading" state.
self.postMessage({ ready: true });
