# difftest/ — differential testing against CRuby

Generates Ruby programs, runs each one under CRuby and under a *system under test*
(SUT), and reports where the outputs differ. The main SUT is the Lean model; others
exist for testing the engine itself and the desugarer.

## Setup

```sh
cd difftest
uv sync                              # Python 3.12+
export DIFFTEST_RUBY=/path/to/ruby   # optional; defaults to Homebrew's CRuby
export ANTHROPIC_API_KEY=...         # only for generating tier-3 programs
```

For `--sut lean`, build the model first: `cd ../ruby-lean && lake build`.

## Usage

```sh
uv run python -m difftest run --tier 0 --sut lean                 # MRI's bootstraptest vs the model
uv run python -m difftest run --tier 1 -n 300 --sut lean --seed 1 # 300 generated programs
uv run python -m difftest run --tier 1 -n 300 --sut desugar --inject-bug   # self-test: must find disagreements
uv run python -m difftest replay corpus/tier3 --sut lean          # replay a saved corpus
uv run pytest
```

Tier 0 needs the bootstraptest corpus harvested first; see
[Reproducing the results](../docs/reproducing.md#the-model-against-cruby).

Each run writes `reports/<timestamp>-<label>/` (gitignored) with `cases.jsonl`
(one record per program), `summary.json` and `report.md`. The exit code is 1 if
anything disagreed.

## Where programs come from

| Tier | Source |
|---|---|
| 0 | MRI's `bootstraptest` suite, about 1300 small self-contained programs |
| 1 | Random programs generated with Hypothesis. Disagreements are shrunk automatically and saved to `corpus/regressions/` |
| 1.5 | Generated programs that probe evaluation order |
| 2 | Mutating real-world Ruby (not built) |
| 3 | Adversarial programs written by Claude, saved in `corpus/tier3/` and replayed for free |
| 4 | Sorbet-annotated programs in `corpus/sorbet/`, for testing Sorbet's own soundness |

## Systems under test

| `--sut` | What it runs |
|---|---|
| `lean` | desugar → RubyCore JSON → the `rubycore` binary |
| `desugar` | desugar → render back to Ruby → CRuby |
| `identity` | CRuby again; a smoke test that must always agree |
| `sig-strip` | the program with Sorbet signatures removed (tier 4) |

A SUT can answer `Unsupported(reason)` for programs outside what it handles. Those
are reported separately, never counted as agreement or disagreement.

## More

- [The difftest engine](../docs/testing/engine.md): each tier in detail, what is
  compared, the SUT interface, the Sorbet probes, and the invariants to keep when
  changing the generators.
- [Testing methodology](../docs/testing/methodology.md): the reasoning behind the
  design. Code comments cite it as *"artifact 05 §N"*.
- [`implementation-notes.md`](implementation-notes.md): numbered implementation
  decisions (N1, N2, …) cited from the code.
