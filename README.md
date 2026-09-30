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
- Sorbet (`sorbet` and `sorbet-runtime` gems).
- [uv](https://docs.astral.sh/uv/) and Python 3.12 or newer for the differential
  tests. uv manages the test environment.
- Git and network access for the optional MRI `bootstraptest` run, which
  downloads test cases on its first run.

On macOS with Homebrew, one way to install them is:

```sh
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
brew install ruby python@3.12 uv
export PATH="$(brew --prefix ruby)/bin:$PATH"
gem install sorbet sorbet-runtime
```

From the repository root, check that the tools are available:

```sh
scripts/check-prereqs.sh
```

The script reports missing tools and installation hints. Also check that
`ruby --version` reports 4.0.x and that Python 3.12 or newer is available
before running the differential tests.

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

   The first differential run fetches a sparse copy of `ruby/ruby`. Set
   `RUBY_SRC` if you want that checkout somewhere other than `/tmp/ruby-src`.
   The script stops at the first failure.

For the individual commands and an explanation of the measurements, see
[Reproducing the results](docs/reproducing.md). To run a
single program through the model after building:

```sh
echo 'puts 1 + 2' | ruby desugar/bin/export-json | ruby-lean/.lake/build/bin/rubycore
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
- [`desugar/`](desugar/README.md): Ruby source to the model's input format.
- [`difftest/`](difftest/README.md): comparison with CRuby.
- [`playground/`](playground/README.md): run and step through programs in a browser.
- [`docs/`](docs/index.md): design, supported Ruby features, and testing method.

For development, read [`CONTRIBUTING.md`](CONTRIBUTING.md) and
[`AGENTS.md`](AGENTS.md). The project is licensed under Apache 2.0; see
[`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
