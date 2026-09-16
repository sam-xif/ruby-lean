# `wasm/` — the executables, for `wasm32-wasip1`

`rubycore` and `validate-one`, compiled to WebAssembly so the playground can be
a static page with no server behind it.

```sh
lake build          # the native build must exist first: this compiles its C
wasm/build.sh       # -> wasm/out/{rubycore,validate-one}.wasm
wasm/ruby/build.sh  # -> wasm/out/ruby.wasm   (the Ruby half; see wasm/ruby/)
```

The page needs both halves. This directory is the Lean side -- the model and
the checker. [`wasm/ruby/`](ruby/README.md) is CRuby: the desugar harness, the
strip chain, and the oracle. All five jobs are stdin -> stdout WASI modules, so
the browser needs one runner rather than three integrations.

Needs [wasi-sdk](https://github.com/WebAssembly/wasi-sdk) (set `$WASI_SDK`, or
unpack it at `~/wasm-tools/wasi-sdk-34.0-arm64-macos`). Intermediates are cached
in `~/.cache/ruby-lean-wasm`; a warm rebuild is seconds, a cold one about three
minutes.

## Sizes

|  | native | wasm |
|---|---|---|
| `validate-one` | 2.88 MB | **5.47 MB** |
| `rubycore` | 4.66 MB | **6.76 MB** |

Both were ~100 MB before `Json/` replaced `import Lean.Data.Json`; see
`Json.lean` for that measurement. A wasm build was not reachable without it.

## Status

Both executables are **exact**. Compared against the native binaries over the
whole corpus, byte-for-byte on stdout, stderr and exit status:

| | cases | result |
|---|---|---|
| `validate-one` | 79 rungs carrying a derivation | 79 agree, 0 disagree |
| `rubycore` (the `Obs` record) | 252 programs | 252 agree, 0 disagree |
| `rubycore --trace 40` (the stepper) | 252 programs | 252 agree, 0 disagree |

Run under `wasmtime -W exceptions=y`.

### What the first run found

Nine programs disagreed before patch 7, all through `String#split` and the
regex paths it shares. `"x-1".split("-")` came back as `["x", "1\u0000\u0000\u0000"]`,
and without `-DNDEBUG` it tripped `assert(i < lean_ctor_num_objs(o))`.

It was not in this model. `string_to_list_core` in the Lean runtime -- the C
behind `String.toList` -- seeds its `List Char` with `lean_box_uint32(0)` as the
`nil`. On 64-bit that is `lean_box(0)`, which *is* `List.nil`, so it is correct
by coincidence. On 32-bit `lean_box_uint32` does not tag a pointer: it
heap-allocates a constructor with a `uint32` scalar field and zero object
fields. The terminator is then not a scalar, so every consumer that walks the
list with `while (!lean_is_scalar(o))` -- `lean_string_mk` first among them --
runs off the end and reads object fields from an object that has none. The
model reached it through `charSlice`, which is `String.mk ((s.toList.drop a).take (b - a))`
and nothing else.

Patch 7 is a one-line fix and the only one of the seven that is a defect rather
than a porting accommodation. It is worth reporting upstream; wasm32 is
plausibly the first 32-bit target anyone has run this code on in a long time.

## How this is built, and why it is smaller than you would expect

It does not port the Lean compiler. Nothing here runs `lean` to elaborate
anything at build time; it compiles C that already exists or that the *native*
`lean` emits:

1. `lake build` leaves this package's C in `.lake/build/ir/` (448 modules).
2. The toolchain ships no C for `Init`/`Std`, but it ships their `.lean` sources
   and `.olean`s, and `lean -c` regenerates that C from them — 1,077 modules in
   about 80 seconds. There is no bootstrap and no second Lean build.
3. The runtime is 26 `.cpp` files. It is *already* written for a target with no
   libuv, no OpenSSL, no threads and no process spawning: that is what
   `LEAN_EMSCRIPTEN` selects, and defining it under wasi-sdk gets most of the
   way. `patch-runtime.py` is the seven-edit remainder — six inside a
   `__wasi__` branch or an added include, plus one real upstream bug fix.

GMP is not needed: leaving `LEAN_USE_GMP` undefined selects the runtime's own
`mpn.cpp` bignums. This is the dependency that stalled every previous attempt.

`shim/` holds what WASI does not have:

| file | what it is |
|---|---|
| `uv.h`, `uv_shim.c` | libuv's *synchronous filesystem* calls — stat, lstat, link, unlink, mkstemp, mkdtemp, tmpdir — over POSIX. Not stubs: `io.cpp` is the one runtime file that reaches for libuv outside the `LEAN_EMSCRIPTEN` guard, and all of it is filesystem work WASI can do. |
| `emscripten.h`, `emscripten/stack.h` | `LEAN_EMSCRIPTEN` brings in one header for three uses: `EM_ASM(debugger)` and two `EM_ASM_INT` calls whose "not available" answer is 0 — which is the honest answer with no JS engine to ask. |
| `wasi_stubs.cpp` | the initializers of the two runtime files that cannot be built at all: `process.cpp` (fork/exec) and `stack_overflow.cpp` (a SIGSEGV handler on an alternate signal stack). The `lean_io_process_*` entry points are deliberately *not* stubbed: nothing in either closure spawns a process, so the linker never asks — and if that changes it will say so rather than silently linking something that cannot work. |

`gen/` is the four headers cmake would have generated. All four values are fixed
for this build, so they are checked in rather than substituted.

## Why WASI and not emscripten

Both executables are stdin → stdout filters. Emscripten's pthread build needs
`SharedArrayBuffer`, which needs COOP/COEP response headers, which GitHub Pages
cannot send — you would be on the `coi-serviceworker` hack. `wasm32-wasip1` is
single-threaded and needs no headers; in the browser it runs under a WASI shim
with stdin and stdout wired to strings.

One flag matters at the far end: the build asks clang for **standard** wasm
exception handling (`-mllvm -wasm-use-legacy-eh=false`) rather than the legacy
encoding it still defaults to. wasmtime 48 rejects the legacy `try`; browsers
want `try_table` too.
