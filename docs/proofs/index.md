# What is proved

Every proof is in `books/`, a Lake package that uses the model as a library. The proofs are organized as *books*: each is a directory under
`books/Books/` with one result at its head.

| Book | Headline result |
|---|---|
| [Type soundness](type-soundness.md) | A program the checker accepts never ends in an uncaught `NoMethodError`, `ArgumentError` or `TypeError` when the model runs it |
| [Metatheory](metatheory.md) | Facts about the model itself: a relational definition of a step agrees with the executable one, and a general type-safety principle that needs no type system |
| [FastPower](../guides/prove-a-program.md) | One Ruby program, exponentiation by squaring, computes `b ** n` for every `b` and `n` |

`books/Books/Lib/` is not a book. It is the machinery for proving things about
a single program.

## Axioms

Every headline theorem depends on `propext`, `Classical.choice` and
`Quot.sound`, the three axioms of Lean's standard library, and on nothing else.
No proof uses `sorry` or `native_decide`. (The one file that contains `sorry`,
`Comparator/Challenge.lean`, states the soundness theorems without proving
them; see below.) The build checks this in three
places, and each fails the build if it changes:

* `#guard_msgs in #print axioms …` next to the theorems themselves;
* `make metatheory` and `make soundness`, which print the axioms of each
  theorem and reject any other;
* `make comparator`, described below.

## Building and checking

From the repository root:

```sh
make books        # build every file under books/Books/
make metatheory   # the metatheory, its axiom audit, and the heap probes
make soundness    # the soundness theorem, its controls, and the corpus
make comparator   # an independent re-check of the soundness theorem
```

The first build of the books takes from several minutes on a many-core machine
to about half an hour on a small one, almost all of it in the type-soundness
book. Rebuilds after a change take seconds to minutes.

A change to the model or the checker can break a proof while the model and the
checker still build, because the proofs are a separate package. `make books`
builds every file of every book, and `make check` and continuous integration
both run it.

## The independent check

`make comparator` runs
[`leanprover/comparator`](https://github.com/leanprover/comparator) on the
soundness theorem. `books/Books/TypeSoundness/Comparator/Challenge.lean` states the three soundness
theorems with `sorry` in place of a proof. The comparator checks that

1. the statements proved in `books/Books/TypeSoundness/Soundness.lean` are
   identical to those, including every definition they mention;
2. the proofs use only the three permitted axioms;
3. a fresh Lean kernel accepts the whole dependency closure.

This does not trust the elaborator or anything a source file could do at
elaboration time. To review what the theorem claims, you read
`Challenge.lean`, not the proof.

The script's header (`books/scripts/run-comparator.sh`) documents two things
that are not stock: a three-line patch to the replay tool, reported upstream as
[lean4#15529](https://github.com/leanprover/lean4/issues/15529), and the fact
that the comparator's sandbox is real only on Linux.

## Controls

A proof development can be vacuously true. The books contain *controls* against
that: programs and derivations the checker must reject, and countermodels
showing why a hypothesis is needed.

* `books/Books/TypeSoundness/Checker/Controls/` and
  `books/Books/TypeSoundness/Controls/` are
  built with everything else, and a control that stops holding fails the build.
* 46 programs in `books/corpus/` are marked as ones the checker must reject, for
  example `1 + true`. `make soundness` fails if one is accepted.
* `bootOkB = true`, a hypothesis of the soundness theorem, is evaluated by the
  build. It says the machine the core library boots into satisfies the
  invariant, and it is what stops the theorem from holding vacuously.
