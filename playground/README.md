# playground

Load an annotated Ruby program, run the typed ladder's five stages over it, and
see what `validateD` — the one trusted Bool — says. Edit the program, or edit
the emitted certificate, and run it again.

```
annotated Ruby
  ├─ 0  signatures   read the declared types
  ├─ 1  strip        sig · visibility · freeze · require · const_inline · class_sugar
  ├─ 2  desugar      harness/desugar-dt → RubyCore JSON
  ├─ 3  derive       the untrusted emitter → a Deriv
  └─ 4  validateD    the trusted Bool                      ← the only claim
```

Beside it, **Lean model ▶** and **CRuby ▶** run the same program through the
model and through real CRuby, and say whether their stdout agrees.

## Two ways to run it

Same `index.html` both times. The only difference is who executes the stages.

**In the browser, no server.** Everything is wasm in a worker: `ruby.wasm` for
the desugar harness, the strip chain, the sig reader, the emitter and the CRuby
oracle; `rubycore.wasm` for the model; `validate-one.wasm` for `validateD`.

```sh
(cd ../ruby-lean && wasm/build.sh && wasm/ruby/build.sh)   # once
./build.sh                    # -> dist/ and dist.tar.gz
./build.sh --serve            # ... and serve it on :8080
```

`dist/` is a static site: drop it on GitHub Pages or open it from disk. Nothing
is fetched from a third party at run time.

**Against localhost, over the native binaries.** The reference implementation,
and the only way to run the real `srb`:

```sh
(cd ../ruby-lean && lake build)
python3 server.py             # http://localhost:8077
```

The page chooses by looking for `config.js`, which `build.sh` writes into
`dist/` and which does not exist in the source tree — so a checkout served by
`server.py` uses the server, and a deployed `dist/` uses wasm. `?backend=wasm`
and `?backend=server` override either, which is how you compare them.

## What the browser cannot do, and does not pretend to

**Sorbet.** It is a C++ binary with no wasm port. `read_sigs.rb` reads the
declared types off the source with Prism instead, which is sound rather than a
shortcut — `Ratchet/Deriv.lean` re-derives every declared type, so a weaker
reader costs blocks and rejects and never a wrong accept.
(`ruby-lean/scripts/cmp_sig_readers.py` measures it: the same 63 rungs accepted
either way.)

Sorbet's *verdict* is a different thing and is not reconstructible. The page
shows the recorded `srb_clean` only while the buffer still matches the corpus
source, and says **"not checked"** the moment you edit. `server.py` runs the
real thing and says so.

## Files

| | |
|---|---|
| `index.html` | the page: five stages, two run buttons, no tabs |
| `js/wasi.js` | a WASI preview1 shim, sized to these five jobs. No filesystem — `ruby.wasm` carries its own via wasi-vfs |
| `js/worker.js` | runs the modules off the main thread and caches compiled ones |
| `js/backend.js` | the seam: nine calls, answered by wasm or by `server.py` |
| `build.sh` | assembles `dist/` and `dist.tar.gz` |
| `mkcorpus.py` | bakes all 259 rungs (metadata, source, recorded verdict) into one `corpus.json` |
| `server.py` | the localhost fallback, nine matching routes |

## Sizes

`dist/` is 57.6 MB on disk, 17.9 MB as `dist.tar.gz`; `ruby.wasm` is 44.7 MB of
that and gzips to about 15 MB, which is roughly what a visitor transfers since
Pages gzips on the wire. Under the 100 MB per-file limit.

The first press of a Ruby stage pays a one-off wasm compile of that 44 MB — a
few seconds. The page prewarms it on load, and the Lean modules (5.5 and 6.8 MB)
are independent, so `validateD` is quick even while Ruby is still warming.
