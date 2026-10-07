# ruby-lean/ — the model and the checker

One Lake package with two libraries that do not import each other.

| Library | Contents |
|---|---|
| [`RubyCore/`](RubyCore/README.md) | The model: an abstract machine for Ruby and its step function, `stepFn`. Builds the `rubycore` executable |
| [`Checker/`](Checker/README.md) | A type checker for a fragment of Sorbet-annotated Ruby. Its entry point is `validateD`. Builds the `validate-one` executable |

Nothing in this package is a proof. Every proof about the model or the checker
is in [`../books/`](../books/README.md), a separate package that uses this one
as a library.

| Path | Contents |
|---|---|
| `prelude/prelude.rb` | The part of Ruby's core library that the model implements in Ruby: `Enumerable`, `Comparable` and about a hundred other methods |
| `prelude/features/` | Libraries that load on `require`: `json`, `uri`, `forwardable`, `pathname`, and a model of `sorbet-runtime` |
| `scripts/` | Generators for the files under `RubyCore/Generated/` and `Checker/Audit/`; the scripts that read signatures (`srb_sigs.py`, `read_sigs.rb`) and propose a typing derivation (`emit_deriv.rb`) |
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
make soundness      # the checker's soundness theorem and its corpus
make books          # every proof
```

After editing `prelude/` or a checker source under `Checker/Check/`, run
`make gen` to regenerate the committed generated files.

## Read next

- [The semantics](../docs/semantics/index.md): what the model says Ruby means,
  with a map of every file under `RubyCore/`.
- [Type soundness](../docs/proofs/type-soundness.md): what the checker's
  acceptance guarantees.
