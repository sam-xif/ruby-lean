# playground/

A browser UI for the whole pipeline. Pick one of the 259 annotated corpus
programs (or write your own), run the five stages on it, and see whether the Lean
checker proves it free of type errors. You can edit the program or the proposed
derivation and check again.

It also runs the program through the Lean model and through CRuby and compares
their output, and **Step it ▶** walks the model one `stepFn` transition at a time,
showing the control state, frames, continuation stack and stdout.

## Running it

Against local binaries (the only way to run the real Sorbet):

```sh
(cd ../ruby-lean && lake build)
python3 server.py             # http://localhost:8077, Python stdlib only
```

Entirely in the browser, with everything compiled to wasm:

```sh
(cd ../ruby-lean && wasm/build.sh && wasm/ruby/build.sh)   # once
./build.sh --serve            # builds dist/ and serves it on :8080
```

`dist/` is a static site you can host anywhere. The page uses wasm when it finds
the `config.js` that `build.sh` writes, and the local server otherwise; add
`?backend=wasm` or `?backend=server` to the URL to override.

In the browser build, Sorbet isn't available, so signatures are read with Prism
instead. This can make the checker reject more, never accept more.

## Testing it

```sh
./build.sh && node --experimental-wasm-exnref check.mjs
```

Runs every backend call against the real wasm modules in `dist/`. It doesn't
render the page, so it checks the pipeline, not the UI.

## More

[The playground](../docs/playground.md) covers the stale-result tracking, the
stepper's window controls, what the browser build can't do, every file, and
download sizes.
