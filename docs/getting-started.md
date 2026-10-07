# Getting started

## Install the tools

| Tool | Version | Used for |
|---|---|---|
| [elan](https://github.com/leanprover/elan) | any | Lean and Lake. The Lean version is pinned in `ruby-lean/lean-toolchain` and elan fetches it |
| CRuby | 4.0.x | The reference the model is checked against, and the interpreter the desugarer runs under |
| Sorbet | pinned in `Gemfile.lock` | Reads the signatures of a typed program |
| [uv](https://docs.astral.sh/uv/) and Python | 3.12 or newer | The differential tests and the corpus pipeline |

On macOS with Homebrew:

```sh
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
brew install ruby python@3.12 uv
export PATH="$(brew --prefix ruby)/bin:$PATH"
make deps        # the gems pinned in Gemfile.lock, Sorbet among them
```

[`mise.toml`](https://github.com/sam-xif/ruby-lean/blob/main/mise.toml) pins the
same versions if you use [mise](https://mise.jdx.dev).

Check that everything is found:

```sh
make prereqs
```

## Build and run

```sh
make run                              # the model, the checker and the desugarer
echo 'puts 1 + 2' | bin/ruby-lean     # prints 3, then "=> nil"
```

The first build compiles the model and takes a few minutes. From here you can
[run programs](guides/run-a-program.md) and
[type-check them](guides/prove-type-safety.md). Neither needs the proofs to be
built.

## Check everything

```sh
make check
```

This is the one command that says whether the repository is sound. It stops at
the first failure, and continuous integration runs the same targets. It:

1. builds the model and the checker (`make lean`);
2. builds every proof book (`make books`). The first build takes from several
   minutes on a many-core machine to about half an hour on a small one, and
   later builds take seconds;
3. audits the axioms behind every headline theorem (`make metatheory`,
   `make soundness`, `make comparator`);
4. runs the checker over its corpus of typed programs and compares the result
   with the recorded one (`make soundness`);
5. runs the model against CRuby over about 1300 programs from CRuby's own test
   suite, and fails on any disagreement (`make conformance`);
6. tests the desugarer against CRuby (`make desugar-test`), runs the
   differential tester's own tests (`make difftest-test`), and compares each
   program book's theorem with what CRuby does (`make book-checks`);
7. builds this documentation with link checking (`make docs`), and checks that
   continuous integration runs every one of these targets (`make ci-sync`).

`make help` lists every target with a one-line description. The first
`make conformance` or `make desugar-test` downloads CRuby's `bootstraptest`
directory (a sparse clone of `ruby/ruby` at the pinned tag) into
`~/.cache/ruby-lean/`.

## Repository layout

| Directory | Contents |
|---|---|
| `ruby-lean/RubyCore/` | The model: the semantics of Ruby, in Lean |
| `ruby-lean/Checker/` | The type checker |
| `ruby-lean/prelude/` | The part of Ruby's core library that the model implements in Ruby |
| `books/` | Every proof, and the corpus of typed programs the checker is measured on |
| `desugar/` | Ruby source to the model's core language |
| `difftest/` | Differential testing against CRuby |
| `playground/` | A browser interface to all of the above |
| `bin/` | `ruby-lean` (run a program) and `ruby-lean-check` (type-check a program) |
| `docs/` | This site |
