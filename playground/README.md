# playground

The user-facing front end. Pick one of 259 annotated Ruby programs, run the five
stages over it, and see whether the Lean checker can prove it will never raise a
type error. Edit the program, or edit the proposed proof, and check it again.

The page is written for someone arriving with no context: **What is this?** in
the header opens an overview covering what the checker proves, why CRuby runs
beside it, what the stepper shows, and — stated plainly — that 63 of the 259
programs are inside the certified fragment today and this is a proof of concept
aimed at the whole language and at programs that read user input.

Corpus descriptions are working notes written for whoever is building the
ladder, so the menu does not show them raw: programs are listed by name and
grouped by tier, and prose appears under the menu only when a clean sentence can
be extracted from the note (48 of 259 have none, and show the name instead).

```
annotated Ruby
  ├─ 0  signatures   read the declared types
  ├─ 1  strip        sig · visibility · freeze · require · const_inline · class_sugar
  ├─ 2  desugar      desugar-dt → RubyCore JSON
  ├─ 3  derive       the untrusted emitter → a Deriv
  └─ 4  validateD    the trusted Bool                      ← the only claim
```

Beside it, **Lean model ▶** and **CRuby ▶** run the same program through the
model and through real CRuby, and say whether their stdout agrees.

And **Step it ▶** opens an overlay that walks the model one `stepFn` transition
at a time — the control state, the call/block frames with their live locals, the
continuation stack and the accumulated stdout. `←` / `→` step while it is open,
`Esc` or a click outside closes it. It is a *printer* over the real
`stepFn` (`ruby-lean/RubyCore/Trace.lean` emits every configuration as JSON
instead of one observation), not a second interpreter, so it has no fragment of
its own: whatever the model runs, this shows.

A whole-program trace is only viable for a toy, so the window controls matter —
**count steps** says how long the program is, **start at** takes a substring of
the rendered control (`send .bump(`) and stops at the first step containing it,
and **or step** jumps to an index. On anything real those are the difference
between a usable view and four thousand steps of prelude boot.

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
shortcut — `Ratchet/Check/Deriv.lean` re-derives every declared type, so a weaker
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
| `js/backend.js` | the seam: eleven calls, answered by wasm or by `server.py` |
| `build.sh` | assembles `dist/` and `dist.tar.gz` |
| `mkcorpus.py` | bakes all 259 rungs (metadata, source, recorded verdict) into one `corpus.json` |
| `server.py` | the localhost fallback, eleven matching routes |
| `check.mjs` | drives the built `dist/` headlessly against the real modules |

## Checking it

```sh
./build.sh && node --experimental-wasm-exnref check.mjs
```

Imports the real `backend.js` / `worker.js` / `wasi.js` out of `dist/` and runs
all eleven calls against the real wasm — including the trace window controls,
and that a recorded Sorbet verdict is withdrawn once the buffer is edited. The node flag enables the standard wasm
exception encoding; browsers need nothing.

It stubs four browser globals, and stubs them *carefully*: `fetch` resolves
through `new URL(u, base)` and the fake `Worker` checks each posted URL the way
a real worker would resolve it — against its own script URL, not the document's.
An earlier version string-munged paths instead and stayed green while the page
was broken, because `backend.js` was handing the worker a relative wasm URL that
resolved to `js/wasm/ruby.wasm`.

It does not render anything, so `index.html`'s own script is unexercised: a
green run means the pipeline works, not that the page looks right.

## Sizes

`dist/` is 57.6 MB on disk, 17.9 MB as `dist.tar.gz`; `ruby.wasm` is 44.7 MB of
that and gzips to about 15 MB, which is roughly what a visitor transfers since
Pages gzips on the wire. Under the 100 MB per-file limit.

The first press of a Ruby stage pays a one-off wasm compile of that 44 MB — a
few seconds. The page prewarms it on load, and the Lean modules (5.5 and 6.8 MB)
are independent, so `validateD` is quick even while Ruby is still warming.
