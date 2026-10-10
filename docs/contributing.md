# Contributing

## The rule

**`make check` must pass before a change is merged.**

```sh
make check
```

It builds the model, the type checker and every proof, audits their axioms,
runs the checker over its corpus, runs the model against CRuby, and builds these
docs. It stops at the first failure and prints which check failed. Continuous
integration runs the same targets on every pull request, and every one of them
blocks the merge. Nothing is report-only, and `make ci-sync` fails if `make
check` gains a target that continuous integration does not run.

While working, run the part you are changing:

| You changed | Run |
|---|---|
| The model (`ruby-lean/RubyCore/`, `ruby-lean/prelude/`) | `make conformance`, then `make books` |
| The checker (`books/Books/TypeSoundness/Checker/`) | `make soundness` |
| A proof (`books/`) | `make books`; `cd books && ./scripts/check-soundness.sh --proofs-only` |
| The desugarer (`desugar/`) | `make desugar-test desugar-coverage` |
| The differential tester (`difftest/`) | `make difftest-test` |
| The docs | `make docs` |

A change to the model can break a proof while `make lean` still passes, because
the proofs are a separate Lake package. Always finish with
`make books`.

## Two boundaries

**The checker imports nothing from the model.**
`books/Books/TypeSoundness/Checker/` has its own copy of the syntax, and imports
nothing from the rest of its book either. The only place the checker and the
model meet is the soundness proof around it. `books/scripts/check-isolation.sh` enforces
this and `make soundness` runs it first.

**Only `validateD` is trusted.** Sorbet, the annotation stripper, the desugarer
and the derivation emitter are untrusted by construction: a bug in one of them
can cost an accepted program, and can never produce a wrongly accepted one. Keep
it that way. If one of them is wrong, fix it there. A change inside the checker
that compensates for a bug upstream trades a false rejection for a possible
false acceptance, which is the one trade this design exists to refuse.

## Recorded results

Four files record a result that a change is not allowed to make worse. Each
check prints what moved and how to record an improvement.

| File | Records | Update with |
|---|---|---|
| `difftest/coverage-baseline.json` | How many `bootstraptest` programs agree with CRuby, and how many the model declines | `scripts/check-conformance.sh --save .make/conformance` |
| `desugar/coverage-baseline.json` | How many `bootstraptest` programs the desugarer supports | `ruby desugar/bin/coverage --save` |
| `books/corpus/accepted.txt` | Exactly which corpus programs the checker accepts | `books/scripts/check-soundness.sh --record` |
| `books/corpus/*.meta.json` | For each corpus program, what Sorbet and the checker are expected to answer | By hand, with the program |

Commit the updated file with the change that caused it, so the diff shows what
moved.

## Generated files

`ruby-lean/RubyCore/Generated/` and `books/Books/TypeSoundness/Checker/Audit/` are written by
scripts and committed. `make gen` regenerates them and `make gen-check` fails if
one is stale. After editing `ruby-lean/prelude/prelude.rb`, a file under
`ruby-lean/prelude/features/`, or a checker source under
`books/Books/TypeSoundness/Checker/Check/`, run `make gen`.

One file in `Generated/` is different. `BootedHeap.lean`, the heap the prelude
boot produces written out as terms, is a build artifact: it is not in the
repository, and `make` writes it before building anything that needs it,
whenever the model has changed. The proof books import it, so build them with
`make books` (or any other `make` target) rather than a bare `lake build` in a
fresh checkout. `Books/Metatheory/Heap/BootedHeap.lean` proves the file equal to
the boot.

## Adding Ruby to the model

1. **Find what is missing.** `bin/ruby-lean --compare prog.rb` prints why a
   program was declined. `ruby desugar/bin/coverage --full` ranks the
   constructs the desugarer lacks by how many test programs each blocks.
2. **Decide where it goes.**
    * *Syntax that can be expressed with existing core forms* is a rewrite in
      `desugar/lib/desugar.rb`. Prefer this: it adds nothing to the model.
    * *A library method that can be written in Ruby* goes in
      `ruby-lean/prelude/prelude.rb`.
    * *A primitive* is a builtin in `ruby-lean/RubyCore/Builtins/`.
    * *A new core form* needs a node in `desugar/lib/rubycore.rb` and
      `ruby-lean/RubyCore/Syntax.lean` (the two lists mirror each other) and a
      case in `stepFn`.
3. **Add a test program** to `desugar/corpus/seeds/`. If the feature has an
   evaluation-order obligation (a receiver evaluated once, operands left to
   right), make the program log each evaluation so the order is observed.
4. **Run** `make desugar-test conformance`. Newly supported programs must agree
   with CRuby. Record the improved baseline.
5. **Run** `make books`. A change to `stepFn` or the heap often needs proofs
   updated.

When the model cannot do something faithfully, make it decline with a reason.
Never approximate: a wrong answer is a disagreement with CRuby, and a declined
program is not.

## Adding a typing rule

A rule enters the checker together with the proof that it is sound.

1. Add the rule as a constructor of the judgment in
   `books/Books/TypeSoundness/Checker/Judgment/`.
2. Prove its semantic obligation in `books/Books/TypeSoundness/Rules/`, and
   import that file from `books/Books/TypeSoundness/Registry/ActiveProofs.lean`.
3. Enable the rule by adding its name to `clinkProfile` in
   `books/Books/TypeSoundness/Checker/ClinkPolicy.lean`. An enabled rule with no proof fails the
   build; a rule that is not enabled is refused by `validateD`.
4. Teach `books/scripts/emit_deriv.rb` to propose the rule. This script is
   untrusted, so it needs no proof.
5. Add a program that needs the rule to `books/corpus/`, and beside it a
   near-identical program that must still be rejected. Each is a `NNN-name.rb`
   with a `NNN-name.meta.json`.
6. Run `make soundness`, then `books/scripts/check-soundness.sh --record` to
   record the newly accepted programs.

## Adding a proof about a program

`bin/new-book Name prog.rb` creates a program book with a first theorem already
proved. See [Prove a program correct](guides/prove-a-program.md).

## Style

* Name files, modules and targets so that someone who has not followed the
  project can tell what they are.
* Documentation describes what the code does now. History belongs in commit
  messages.
* A proof file has no `sorry`, no `native_decide` and no new axiom.
