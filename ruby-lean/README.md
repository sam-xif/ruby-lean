# ruby-lean/ — the model

A Lake package holding the model: [`RubyCore/`](RubyCore/README.md), an abstract
machine for Ruby with its step function `stepFn`, and the `rubycore` executable
that runs it.

Nothing in this package is a proof, and nothing in it is a type checker. Both
are in [`../books/`](../books/README.md), a separate package that uses this one
as a library.

| Path | Contents |
|---|---|
| `RubyCore/` | The model |
| `prelude/prelude.rb` | The part of Ruby's core library that the model implements in Ruby: `Enumerable`, `Comparable` and about a hundred other methods |
| `prelude/features/` | Libraries that load on `require`: `json`, `uri`, `forwardable`, `pathname`, and a model of `sorbet-runtime` |
| `scripts/` | Generators for the files under `RubyCore/Generated/`, and the check of `require` against CRuby |
| `Json/` | A copy of Lean's JSON library, so that the executables do not link all of Lean |
| `wasm/` | Builds the WebAssembly modules the [playground](../playground/README.md) runs |

## Build and run

From the repository root, `make run` builds what is needed and
[`bin/ruby-lean`](../docs/guides/run-a-program.md) runs a program. By hand:

```sh
lake build                    # the toolchain is pinned in lean-toolchain
echo 'puts 1 + 2' | ruby ../desugar/bin/export-json | .lake/build/bin/rubycore
```

`rubycore` reads a program in the core language as JSON and prints what running
it is observed to do. It exits 0 on success, 3 when the program uses something
the model does not support (with the reason on stderr), and 1 on bad input or a
bug in the model.

## After a change

A change here can break a proof in `../books/` without breaking this package's
build. From the repository root:

```sh
make conformance    # the model against CRuby
make books          # every proof
```

After editing `prelude/`, run `make gen` to regenerate the committed generated
files.

## Read next

- [The semantics](../docs/semantics/index.md): what the model says Ruby means,
  with a map of every file under `RubyCore/`.
- [What is proved](../docs/proofs/index.md) about it.
