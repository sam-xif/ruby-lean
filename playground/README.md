# playground/

A browser interface to the whole pipeline. Pick one of the typed corpus programs
or write your own, run the stages on it, and see whether the checker accepts it.
It also runs the program on the model and under CRuby and compares their output,
and **Step it ▶** walks the model one `stepFn` transition at a time.

## Running it

Against local binaries, which is the only way to run the real Sorbet:

```sh
make -C .. run
python3 server.py             # http://localhost:8077, Python standard library only
```

Entirely in the browser, with everything compiled to WebAssembly:

```sh
make -C .. playground-serve   # builds the wasm modules and dist/, serves on :8080
```

`dist/` is a static site you can host anywhere.

## Testing it

```sh
./build.sh && node --experimental-wasm-exnref check.mjs
```

[The playground](../docs/playground.md) describes the page, what the browser
build cannot do, and each file here.
