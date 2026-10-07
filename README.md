# ruby-lean

`ruby-lean` is an executable model of Ruby written in Lean 4. It runs Ruby
programs after a desugaring step, and its behavior is checked against CRuby. The
repository also contains a type validator for a subset of Sorbet-annotated Ruby.
Lean proves that a program accepted by the validator cannot reach a
`NoMethodError`, `ArgumentError`, or `TypeError` in the model.

The [project write-up](https://samx.io/blog/topics/devlog/2026-09-26-ruby-lean.html)
explains the motivation, the proof, and the limits in more detail. You can also
try programs in the [playground](playground/README.md).

## Prerequisites

You need:

- [elan](https://github.com/leanprover/elan) for Lean and Lake. The Lean version
  is pinned in [`ruby-lean/lean-toolchain`](ruby-lean/lean-toolchain).
- CRuby 4.0.x, available as `ruby` on your `PATH`.
- Sorbet (`sorbet` and `sorbet-runtime` gems), pinned in [`Gemfile.lock`](Gemfile.lock).
- [uv](https://docs.astral.sh/uv/) and Python 3.12 or newer for the differential
  tests. uv manages the test environment.
- Git and network access for the optional MRI `bootstraptest` run, which
  downloads test cases on its first run.
- For the playground's WebAssembly build only: `wasmtime`. The build fetches
  its own wasi-sdk.

[`mise.toml`](mise.toml) pins the non-Lean tool versions if you use
[mise](https://mise.jdx.dev).

On macOS with Homebrew, one way to install them is:

```sh
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
brew install ruby python@3.12 uv
export PATH="$(brew --prefix ruby)/bin:$PATH"
make deps        # the pinned gems from Gemfile.lock
```

From the repository root, check that the tools are available:

```sh
make prereqs
```

The script reports missing tools and installation hints. Also check that
`ruby --version` reports 4.0.x and that Python 3.12 or newer is available
before running the differential tests.

## Build targets

`make` from the repository root drives everything; `make help` lists the
targets. The main ones:

| Target | Builds or runs |
|---|---|
| `make lean` | The Lean package: the model, the validator and its soundness proof |
| `make run` | `rubycore` and the desugarer, for [`bin/ruby-lean`](bin/ruby-lean) (`make run FILE=prog.rb` also runs it) |
| `make desugar` | The desugarer, `desugar/bin/export-json` (Ruby to the model's JSON) |
| `make difftest` | The differential-test environment; then `cd difftest && uv run difftest --help` |
| `make bootstraptest` | The model vs CRuby over MRI's `bootstraptest` |
| `make proofs` | The metatheory (`RubyCore/Proof/`), plus a check of every headline theorem's axioms |
| `make books` | The proof books (`books/`): Ruby programs proved correct against the model |
| `make wasm`, `make playground` | The three WebAssembly modules, then the static playground in `playground/dist/` |
| `make gate` | The typed ratchet gate, which must print `GREEN` before a commit |
| `make check` | Generated-source freshness, the desugar and difftest suites, and the gate |
| `make gen`, `make gen-check` | Regenerate, or check, the committed Lean files generated from Ruby |
| `make docs` | The documentation site in `site/` |

Each part keeps its own tool (Lake, uv, Bundler); the Makefile adds the links
between them. For example, `RubyCore/Prelude.lean` is regenerated when the
desugarer changes, and `make wasm` relinks only after Lake does.

## Reproduce the results

Run these commands from the repository root. A cold Lean build can take around
half an hour; later runs are faster.

1. Build the model and validator, then run the typed corpus and its checks:

   ```sh
   scripts/reproduce.sh
   ```

   Look for `RATCHET GREEN` in the gate output: every accepted corpus program is
   then covered by the proof, and the model agrees with CRuby on the programs
   checked by the gate. If a step fails, the script stops and reports where.

2. To also compare the model with MRI's `bootstraptest` programs and check the
   model's separate metatheory, run:

   ```sh
   scripts/reproduce.sh --with-difftest --with-proofs
   ```

   The first differential run fetches a sparse copy of `ruby/ruby` at the pinned
   tag (`RUBY_REF`, default `v4.0.5`) into `~/.cache/ruby-lean/`; set `RUBY_SRC`
   to put it elsewhere.
   The script stops at the first failure.

For the individual commands and an explanation of the measurements, see
[Reproducing the results](docs/reproducing.md). To run a
single program through the model after `make run`:

```sh
bin/ruby-lean prog.rb            # or: echo 'puts 1 + 2' | bin/ruby-lean
```

## What the result means

The validator checks a proposed type derivation. Sorbet, annotation stripping,
desugaring, and derivation generation may cause a program to be declined; only
the final Lean validator can accept it. The proof concerns execution by this
repository's Ruby model. Differential tests compare that model with CRuby, but
do not establish that they agree on every Ruby program.

The model and the typed fragment are both incomplete. Acceptance rules out the
three type-error classes above; it does not prove termination or rule out other
exceptions. The gate reports current coverage and disagreements rather than
relying on numbers recorded in this README.

## Where to read next

- [`ruby-lean/`](ruby-lean/README.md): the Lean model, validator, proofs, and gate.
- [`books/`](books/README.md): Ruby programs proved correct against the model.
- [`desugar/`](desugar/README.md): Ruby source to the model's input format.
- [`difftest/`](difftest/README.md): comparison with CRuby.
- [`playground/`](playground/README.md): run and step through programs in a browser.
- [`docs/`](docs/index.md): design, supported Ruby features, and testing method.

For development, read [`CONTRIBUTING.md`](CONTRIBUTING.md) and
[`AGENTS.md`](AGENTS.md). The project is licensed under Apache 2.0; see
[`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
