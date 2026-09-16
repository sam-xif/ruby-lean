# `wasm/ruby/` — CRuby, for the browser

```sh
wasm/ruby/build.sh      # -> wasm/out/ruby.wasm   (44.7 MB, 14.9 MB gzipped)
wasm/ruby/verify.sh     # the differential, against the host's own CRuby
```

One self-contained module doing the five Ruby jobs the playground needs:

| job | what runs | invoked as |
|---|---|---|
| desugar | `harness/desugar-dt/bin/export-json` | `ruby.wasm /opt/desugar/bin/export-json` |
| strip chain | `difftest/ruby/*_strip.rb`, six stages | `ruby.wasm /opt/strip/<stage>.rb` |
| CRuby oracle | the user's program | `ruby.wasm` with the source on stdin |
| sig reading | `scripts/read_sigs.rb` (Prism, replaces `srb_sigs.py`) | `ruby.wasm /opt/deriv/read_sigs.rb` |
| derivation | `scripts/emit_deriv.rb` (port of `emit_deriv.py`) | `ruby.wasm /opt/deriv/emit_deriv.rb` |

Everything reads stdin and writes stdout, like the Lean modules beside it, so
the page needs one WASI runner rather than five integrations.

Nothing in `harness/` or `difftest/ruby/` was modified or forked. The files are
copied into the image exactly as they sit in the tree.

## Status

Against the host's CRuby (4.0.5, prism 1.8.1) over all 259 corpus programs:

| job | compared on | result |
|---|---|---|
| desugar | stdout, stderr, exit status | **259 agree, 0 disagree** |
| strip chain | stdout, stderr, exit status | **259 agree, 0 disagree** |
| deriv | the emitted `Deriv`, byte for byte | **259 agree, 0 disagree** |
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

## Deriving without Sorbet

The page can re-derive for a program the user has **edited**, not only replay a
stored rung. That needed the typed ladder's two untrusted stages in Ruby:
`emit_deriv.rb` (a port of `emit_deriv.py`) and `read_sigs.rb` (a Prism reader
standing in for `srb_sigs.py`, since Sorbet is C++ and has no wasm port).

Shipping each rung's stored `sigs.json` instead would have worked only until the
first edit: rename a method and the emitter blocks with "no signature for";
change a `sig` and it proposes the *old* declared type, so `validateD` rejects
the program the user just fixed.

Reading signatures off the source is sound rather than a shortcut, and the
argument is `Ratchet/Deriv.lean`'s, not ours:

> a declared type cannot produce a wrong accept: it arrives as a field of
> `Deriv.defDecl`, and the checker re-checks the body at exactly that type. A
> wrong signature produces a body that fails to certify.

Signatures are certificate *data*. A reader weaker than Sorbet costs
completeness -- earlier blocks, more rejects -- and cannot cost soundness.

`scripts/cmp_sig_readers.py` measures it, comparing Sorbet+Python against
Prism+Ruby over every rung and judging by what `validateD` says:

```
validateD verdict: 252 identical, 0 differ
  rungs accepted, Sorbet path: 63
  rungs accepted, Prism path:  63
```

63 is the typed ratchet's `fragment 63`. The emitted derivations differ on 7 of
252, all of them block-vs-block with a different *reason* -- Sorbet prints a
proc's parameter as `arg0` where the source says `x`; Sorbet resolves
`attr_reader` and `alias` into methods this reader does not see. No rung changes
acceptance.

### One case worth keeping

An earlier version of the reader did not descend into method bodies, so it
missed the nested `def` in rung 236 -- the regression test for
`found-issues.md` §F3, an **unsafe** program whose whole point is that a nested
`def` silently replaces an installed method. The emitter, told only about the
outer signature, proposed a derivation Sorbet's path never would.

`validateD` returned `false`. The rung stayed correctly uncertified, one stage
later than before. That is the trust argument doing its job rather than being
quoted: a weaker reader produced a wrong proposal and the checker caught it.
The reader now descends into method bodies, so the two paths agree again -- but
the failure mode was the one the design promises, and it is worth having seen.

### What is not faked

Sorbet's **verdict** -- `srb_clean`, `srb_diagnostics`, a rung's
`expect_sorbet` -- cannot be reproduced without Sorbet. `read_sigs.rb` reports
`"sorbet": null` and `"verdict": "not-checked"` rather than inventing one, and
the page should show the stored verdict only while the buffer matches the corpus
source, switching to "not checked" on the first edit. Also unavailable:
cross-file resolution, type aliases, and `sig`s declared in a class the file
cannot see. Inheritance *within* the file still works, because the emitter walks
superclasses itself.

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
