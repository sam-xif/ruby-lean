# books/ — the proofs

[`../ruby-lean`](../ruby-lean/README.md) holds the two things that proofs are
about: an executable model of Ruby (`RubyCore/`) and a type checker for
Sorbet-annotated programs (`Checker/`). This package uses it as a library and
holds every proof, as a collection of *books*. A book is a directory under
[`Books/`](Books/) with one result at its head.

| Book | What it proves | Start at |
|---|---|---|
| [`Books/TypeSoundness/`](Books/TypeSoundness/README.md) | A program the checker accepts never ends in an uncaught `NoMethodError`, `ArgumentError` or `TypeError` when the model runs it | [`Soundness.lean`](Books/TypeSoundness/Soundness.lean) |
| [`Books/Metatheory/`](Books/Metatheory/README.md) | Facts about the model itself: the step relation and the executable `stepFn` agree, and a type-safety principle that needs no type system | [`Machine/Step.lean`](Books/Metatheory/Machine/Step.lean) |
| [`Books/FastPower/`](Books/FastPower/README.md) | One Ruby program, exponentiation by squaring, computes `b ** n` for every `b` and `n` | [`Proof.lean`](Books/FastPower/Proof.lean) |

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

Or here, directly:

```sh
lake build
./scripts/check-metatheory.sh
./scripts/check-soundness.sh        # --proofs-only skips the corpus
./scripts/run-comparator.sh
```

The first build takes from several minutes on a many-core machine to about half
an hour on a small one, almost all of it in `Books/TypeSoundness/`. Rebuilds after a change take seconds to minutes.

Each book is one Lake library over its whole directory, so `lake build` compiles
every file under `Books/`.

## Layout

| Path | Contents |
|---|---|
| `Books/` | The books |
| `corpus/` | 266 Sorbet-annotated Ruby programs the checker is measured on. Each `NNN-name.rb` has a `NNN-name.meta.json` saying what Sorbet and the checker are expected to answer. `accepted.txt` records which ones the checker accepts |
| `scripts/` | The checks above; `build_corpus.py`, which runs each corpus program through Sorbet, the desugarer and the derivation emitter; `probes/`, which decide facts about the booted heap |
| `Comparator/` | The statement-only restatement of the soundness theorems that the comparator checks against |
| `CorpusReport.lean` | The executable that prints the corpus report |
| `build/` | Output of `build_corpus.py`. Not committed |

[What is proved](../docs/proofs/index.md) describes the results and how they
are checked.
