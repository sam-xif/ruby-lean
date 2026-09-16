# `wasm/ruby/` — CRuby, for the browser

```sh
wasm/ruby/build.sh      # -> wasm/out/ruby.wasm   (44.7 MB, 14.9 MB gzipped)
wasm/ruby/verify.sh     # the differential, against the host's own CRuby
```

One self-contained module doing the three Ruby jobs the playground needs:

| job | what runs | invoked as |
|---|---|---|
| desugar | `harness/desugar-dt/bin/export-json` | `ruby.wasm /opt/desugar/bin/export-json` |
| strip chain | `difftest/ruby/*_strip.rb`, six stages | `ruby.wasm /opt/strip/<stage>.rb` |
| CRuby oracle | the user's program | `ruby.wasm` with the source on stdin |

Everything reads stdin and writes stdout, like the Lean modules beside it, so
the page needs one WASI runner rather than three integrations.

Nothing in `harness/` or `difftest/ruby/` was modified or forked. The files are
copied into the image exactly as they sit in the tree.

## Status

Against the host's CRuby (4.0.5, prism 1.8.1) over all 259 corpus programs:

| job | compared on | result |
|---|---|---|
| desugar | stdout, stderr, exit status | **259 agree, 0 disagree** |
| strip chain | stdout, stderr, exit status | **259 agree, 0 disagree** |
| oracle | stdout, stderr, exit status | **259 agree, 0 disagree** |

The image is Ruby 4.0.0 with prism 1.7.0, against a host on 4.0.5 / prism 1.8.1.
The skew changes nothing across this corpus -- worth knowing, since the desugar
reads prism's AST and a prism change is exactly the kind of thing that would
move these numbers.

### Feeding the oracle on stdin is not just convenience

There is no writable filesystem in the packed module and none in a browser tab,
so the program has to arrive on stdin. That also makes the comparison *stricter*
than `server.py`'s: with no script file on disk, `error_highlight` cannot read
source back to print a snippet, so it stays quiet on the host too and stderr
matches byte for byte instead of approximately.

One `error_highlight` feature survives that, and `verify.sh` normalises it
symmetrically rather than hiding it: on an arity mismatch the host appends
`caller:` / `callee:` location lines, which need no file. The ruby.wasm build
has no `RubyVM::AbstractSyntaxTree`, so it emits none. Exception class, message,
backtrace and exit status are identical; only those annotation lines differ, on
one program in the corpus.

## What goes into the image

Built from the [ruby.wasm](https://github.com/ruby/ruby.wasm) nightly
`ruby-4.0-wasm32-unknown-wasip1-full`, packed with
[wasi-vfs](https://github.com/kateinoigakukun/wasi-vfs). Both are pinned in
`build.sh` and cached under `~/.cache/ruby-lean-wasm/ruby`.

Three things the distribution ships are deliberately *not* packed: the 24 MB
`libruby-static.a` and the C headers, which exist for building extensions, and
`bin/ruby` itself -- packing that would put the interpreter inside its own
filesystem. Dropping them took the image from 111 MB to 50.7 MB, which also got
it under GitHub Pages' 100 MB per-file limit.

`prune.py` then drops 20 default gems -- documentation, the REPL, test
frameworks, build tools, network protocol clients -- for another 5.8 MB. The
rest of the standard library stays, on purpose: the oracle runs *user* source,
and a `require` that works in their terminal should work in the page.

**`sorbet-runtime` is vendored from the host** (`gem which sorbet-runtime`) into
`site_ruby`, because eleven corpus programs require it and it is not a default
gem. `site_ruby` rather than an installed gem: it is on the default load path,
so `require` finds it with no RubyGems activation and no gemspec to keep in
sync. If the host has no `sorbet-runtime`, `build.sh` warns and those eleven
programs will fail in the oracle.

## The two halves, connected

Both ends of the playground's pipeline now run with no native binary anywhere:

```
$ printf '%s' "$SRC" | wasmtime wasm/out/ruby.wasm /opt/desugar/bin/export-json \
                     | wasmtime -W exceptions=y wasm/out/rubycore.wasm
{"exception":null,"result_repr":"nil","stdout":"7\n","timed_out":false}

$ printf '%s' "$SRC" | wasmtime wasm/out/ruby.wasm
7
```

Model and oracle agree, which is the comparison the page exists to show.
