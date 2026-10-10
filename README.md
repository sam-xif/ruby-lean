# ruby-lean

`ruby-lean` is a model of the Ruby language written in Lean 4. The model is
executable: it runs Ruby programs, and every build checks its behavior against
CRuby. Because it is written in Lean, you can also prove things about what a
Ruby program does.

```console
$ bin/ruby-lean point.rb            # run a program on the model
=> 1

$ bin/ruby-lean-check point.rb      # can it raise a type error?
ACCEPTED  point.rb
  validateD accepted this program. By validateD_safe_run, running it on the
  model never ends in an uncaught NoMethodError, ArgumentError or TypeError.
```

## What you can do

| You want to | Start here |
|---|---|
| Run a Ruby program on the model and compare it with CRuby | [Run a program](docs/guides/run-a-program.md) |
| Show that a Sorbet-annotated program never raises `NoMethodError`, `ArgumentError` or `TypeError` | [Prove a program type-safe](docs/guides/prove-type-safety.md) |
| Prove what a program computes, for every input | [Prove a program correct](docs/guides/prove-a-program.md) |
| Read what the model says Ruby means | [The semantics](docs/semantics/index.md) |
| See what has been proved and what it rests on | [What is proved](docs/proofs/index.md), [What you have to trust](docs/proofs/trust.md) |
| Try it without installing anything | [The playground](docs/playground.md) |

The [project write-up](https://samx.io/blog/topics/devlog/2026-09-26-ruby-lean.html)
explains the motivation.

## Quick start

You need [elan](https://github.com/leanprover/elan) (Lean), CRuby 4.0.x,
[uv](https://docs.astral.sh/uv/) and Python 3.12 or newer. On macOS:

```sh
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
brew install ruby python@3.12 uv
export PATH="$(brew --prefix ruby)/bin:$PATH"
make deps       # the pinned gems, Sorbet among them
make prereqs    # reports anything missing
```

Then:

```sh
make run                              # build the model, the checker and the desugarer
echo 'puts 1 + 2' | bin/ruby-lean     # 3
```

[Getting started](docs/getting-started.md) has the details.

## Checking everything

```sh
make check
```

One command builds the model, the type checker and every proof, audits the
axioms behind each theorem, runs the checker over its corpus of typed programs,
and runs the model against CRuby over more than 1800 programs. It stops at the first
failure. Continuous integration runs the same targets on every pull request and
each one blocks the merge. `make help` lists the individual targets.

A first run spends most of its time compiling proofs: several minutes on a
many-core machine, about half an hour on a small one. Later runs take a few
minutes.

## What is here

| Directory | Contents |
|---|---|
| [`ruby-lean/RubyCore/`](ruby-lean/RubyCore/README.md) | The model: an abstract machine for Ruby, and its step function `stepFn` |
| [`books/`](books/README.md) | Every proof: facts about the model, proofs about individual programs, and the type-soundness book |
| [`books/Books/TypeSoundness/`](books/Books/TypeSoundness/README.md) | A [type checker](books/Books/TypeSoundness/Checker/README.md) for a fragment of Sorbet-annotated Ruby, and the proof that what it accepts is safe |
| [`desugar/`](desugar/README.md) | Ruby source to the core language the model runs |
| [`difftest/`](difftest/README.md) | Differential testing against CRuby |
| [`playground/`](playground/README.md) | A browser interface: run, type-check and step through programs |
| [`docs/`](docs/index.md) | The documentation site (`make docs-serve`) |

## What the results mean

The theorems are about the model. The model is tested against CRuby 4.0.5 on
every build, and that is testing, not proof: it does not establish that the two
agree on every program.

The model does not cover all of Ruby, and the type checker covers less than the
model. When either meets something it does not support, it says so and stops.
It does not guess. Type safety rules out three classes of exception; it does not
prove termination or rule out other exceptions.

[What you have to trust](docs/proofs/trust.md) is the full list.

## Contributing

`make check` must pass. See [Contributing](docs/contributing.md).

Licensed under Apache 2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
