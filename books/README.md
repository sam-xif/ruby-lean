# books/ — the proofs

[`../ruby-lean`](../ruby-lean/README.md) holds an executable model of Ruby
(`RubyCore/`). This package uses it as a library and holds every proof about
it, as a collection of *books*. A book is a directory under
[`Books/`](Books/) with one result at its head.

| Book | What it proves | Start at |
|---|---|---|
| [`Books/TypeSoundness/`](Books/TypeSoundness/README.md) | A type checker for Sorbet-annotated Ruby ([`Checker/`](Books/TypeSoundness/Checker/README.md)), and the theorem that a program it accepts never ends in an uncaught `NoMethodError`, `ArgumentError` or `TypeError` when the model runs it | [`Soundness.lean`](Books/TypeSoundness/Soundness.lean) |
| [`Books/Metatheory/`](Books/Metatheory/README.md) | Facts about the model itself: the step relation and the executable `stepFn` agree, and a type-safety principle that needs no type system | [`Machine/Step.lean`](Books/Metatheory/Machine/Step.lean) |
| [`Books/FastPower/`](Books/FastPower/README.md) | Two Ruby programs, a simple loop and exponentiation by squaring, both compute `b ** n` for every `b` and `n`, and the second takes fewer steps for every `n` from 6 up | [`Faster.lean`](Books/FastPower/Faster.lean) |

[`Books/Lib/`](Books/Lib/) is not a book. It is the machinery for proving things
about a single program. To start a proof about your own program, run
`bin/new-book Name prog.rb` from the repository root; see
[Prove a program correct](../docs/guides/prove-a-program.md).

Every headline theorem depends on `propext`, `Classical.choice` and `Quot.sound`
and nothing else. The checks below fail if that changes.

## Build and check

From the repository root:

```sh
make books        # build every file under Books/
make metatheory   # the metatheory: build, axiom audit, heap probes
make soundness    # the soundness theorem, its controls, and the checker on the corpus
make comparator   # an independent re-check of the soundness theorem
```

Each check is a script inside its book, and can be run directly:

```sh
lake build                                           # here: every book
Books/Metatheory/scripts/check-metatheory.sh
Books/TypeSoundness/scripts/check-soundness.sh       # --proofs-only skips the corpus
Books/TypeSoundness/scripts/run-comparator.sh
```

The first build takes from several minutes on a many-core machine to about half
an hour on a small one, almost all of it in `Books/TypeSoundness/`. Rebuilds after a change take seconds to minutes.

Each book is one Lake library over its whole directory, so `lake build` compiles
every file under `Books/`.

## Layout

This directory is a Lake package and nothing else: `lakefile.toml`, and
[`Books/`](Books/). Everything a book needs is inside its own directory. The
type-soundness book, for example, holds its checker, its corpus of typed
programs and the scripts that run them.

[What is proved](../docs/proofs/index.md) describes the results and how they
are checked.
