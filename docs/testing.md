# How the model is tested

Every theorem in this repository is about the model. Whether the model is Ruby
is an empirical question, and it is answered by running the model and CRuby on
the same programs and comparing what they do. This runs on every build.

## What is compared

Both sides produce an *observation* of a run:

* everything written to standard output,
* the `inspect` of the program's final value,
* the class and message of an uncaught exception, if there was one.

Two runs agree when their observations are equal, character for character. A
program that deterministically raises `NoMethodError` is a perfectly good test:
the model has to raise the same exception with the same message.

The model can also answer **unsupported**, with a reason, for a program that
uses something it does not cover. That is reported separately. It is never
counted as agreement, and never as disagreement.

## What runs on every build

`make check` and continuous integration run all of these, and each fails the
build.

| Target | Programs | Fails when |
|---|---|---|
| `make conformance` | The 1287 programs of CRuby's `bootstraptest` suite | The model and CRuby disagree on any program; or fewer programs agree, or more are unsupported, than the recorded baseline |
| `make conformance` | 219 minimized reproducers of every disagreement found in the past (`difftest/corpus/regressions/`) | Any disagrees |
| `make conformance` | Hand-written adversarial programs for blocks and jumps, dispatch, evaluation order, exceptions, keyword arguments, metaprogramming and namespaces (`difftest/corpus/tier3/`) | Any disagrees |
| `make soundness` | The 267 typed programs of `books/corpus/` | Any disagrees |
| `make feature-loading` | `require`: scope, caching, re-entry and retry after a failed load | The model and CRuby differ |
| `make book-checks` | Each program book's program, on a grid of inputs | CRuby, the model and the theorem do not all agree |
| `make difftest-test` | The differential tester's own unit tests, including the Sorbet probes | Any test fails, or is skipped because a tool is missing |
| `make desugar-test` | Every program in `desugar/corpus/` | The desugared program behaves differently from the original under CRuby |
| `make desugar-coverage` | `bootstraptest` | The desugarer supports fewer programs than the recorded baseline |

### The baseline

`difftest/coverage-baseline.json` records how many `bootstraptest` programs
ran, how many agree and how many are unsupported. The numbers may only improve:
`scripts/check-conformance.sh` fails the build if agreement falls or the
unsupported count rises, and disagreement must be zero. The number of programs
must match exactly, because the corpus is fixed: it is extracted from CRuby's
source at a pinned tag. When a change improves the numbers, record the new ones
in the same change:

```sh
make conformance
scripts/check-conformance.sh --save .make/conformance
```

`bootstraptest` is not stored in this repository. The first run makes a sparse
clone of `ruby/ruby` at the pinned tag (`RUBY_REF` in the Makefile) into
`~/.cache/ruby-lean/` and extracts the test programs from it.

## The desugarer

The model runs a core language, and `desugar/` translates Ruby into it. A bug
there would make the model run the wrong program, so the desugarer is tested on
its own, with CRuby alone.

For a program `P`, `desugar/` translates it to the core language, prints the
core program back as Ruby, and checks that CRuby produces the same observation
for both:

```
P ──desugar──▶ core ──render──▶ P′        observe(P) = observe(P′) under CRuby
```

Comparing values is not enough here. The point of desugaring is to make
evaluation order explicit, and a translation of `a && b` that evaluates `a`
twice usually returns the same value. So the test programs log each
subexpression as it is evaluated, and the logs must match in order and in
count. `ruby desugar/bin/run --bug` injects that double evaluation and shows the
test catching it.

## Generated programs

`difftest/` can also generate programs. These campaigns are not part of the
build, because they are randomized. What they find is: each disagreement is
shrunk to a minimal program and saved under `difftest/corpus/regressions/`,
which every build replays.

```sh
cd difftest
uv run difftest run --tier 1 -n 300 --sut lean --seed 1    # random programs
uv run difftest run --tier 1.5 -n 300 --sut lean           # programs that probe evaluation order
uv run difftest run --tier 1 -n 300 --sut desugar --inject-bug   # self-test: must find disagreements
```

The generator is scope-aware: it only refers to names that are bound, so the
programs it produces run deep into nested constructs and do not stop at a
`NameError` on the first line.

| `--sut` | What is compared with CRuby |
|---|---|
| `lean` | The model: desugar, then `rubycore` |
| `desugar` | The desugarer alone: desugar, print back as Ruby, run under CRuby |
| `identity` | CRuby again. A smoke test of the harness that must always agree |
| `sig-strip` | The program with its Sorbet signatures removed |

Each run writes `cases.jsonl` (one record per program), `summary.json` and
`report.md` to its output directory, and exits with status 1 if anything
disagreed.

## Reading a failure

After a failing `make conformance`, `.make/conformance/report.md` lists the
disagreeing programs with both observations. To work on one:

```sh
bin/ruby-lean --compare path/to/program.rb
```
