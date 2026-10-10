# The playground

A browser interface to the whole pipeline. Pick one of the typed corpus
programs or write your own, run the five stages over it, and see whether the
checker accepts it. You can edit the program, or edit the proposed typing
derivation, and check again.

```
annotated Ruby
  ├─ 0  signatures   read the declared types
  ├─ 1  strip        remove the annotations
  ├─ 2  desugar      Ruby to the model's core language
  ├─ 3  derive       propose a typing derivation (untrusted)
  └─ 4  validateD    the checker's verdict (the only trusted stage)
```

Beside the stages, **Lean model ▶** and **CRuby ▶** run the same program on the
model and under CRuby and say whether their output agrees.

**Step it ▶** walks the model one `stepFn` transition at a time, showing the
control, the frames with their locals, the continuation stack and the output so
far. `←` and `→` step; `Esc` closes it. It prints the states of the real model
(`ruby-lean/RubyCore/Trace.lean`); it is not a second interpreter. A whole
program is long, so the window has controls: **count steps** says how many
steps the program takes, **start at** begins at the first step whose control
contains the text you give (`send .bump(`), and **or step** jumps to an index.

Every result on the page remembers the text it was computed from. When you edit
a box, results that no longer match are dimmed and marked **stale** until you
run again.

## Running it

**Against local binaries.** This is the only way to run the real Sorbet.

```sh
make run
cd playground && python3 server.py      # http://localhost:8077, Python standard library only
```

**Entirely in the browser.** Everything is compiled to WebAssembly and runs in
a worker: CRuby with the desugarer and the pipeline scripts, the model, and the
checker.

```sh
make playground-serve     # builds the wasm modules and playground/dist/, serves on :8080
```

`playground/dist/` is a static site that can be hosted anywhere. Nothing is
fetched from a third party at run time. Building it needs `wasmtime`; the build
downloads its own wasi-sdk.

The page uses WebAssembly when it finds the `config.js` that the build writes
into `dist/`, and the local server otherwise. `?backend=wasm` and
`?backend=server` override that.

## What the browser build cannot do

Sorbet is a C++ program with no WebAssembly port. In the browser the signatures
are read from the source with Prism instead (`books/Books/TypeSoundness/scripts/read_sigs.rb`).
This cannot make the checker accept more: the checker re-derives every declared
type, so a weaker reader can only lead to more programs being declined.

Sorbet's own verdict on a program cannot be reconstructed. For an unedited
corpus program the page shows the recorded verdict, and once you edit it shows
"not checked".

## Testing it

```sh
cd playground && ./build.sh && node --experimental-wasm-exnref check.mjs
```

This runs every backend call against the real WebAssembly modules in `dist/`.
It does not render the page, so it checks the pipeline and not the layout.

## Files

| File | Contents |
|---|---|
| `index.html` | The page |
| `js/backend.js` | The calls the page makes, answered by WebAssembly or by `server.py` |
| `js/worker.js` | Runs the modules off the main thread and caches the compiled ones |
| `js/wasi.js` | A small WASI shim |
| `server.py` | The local server |
| `build.sh`, `mkcorpus.py` | Assemble `dist/` and bake the corpus into one JSON file |
| `check.mjs` | The headless test |
