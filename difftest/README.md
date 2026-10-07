# difftest/ — differential testing against CRuby

Runs a Ruby program under CRuby and under a *system under test*, and reports
where what they do differs. The main system under test is the Lean model.

```sh
make conformance      # from the repository root; what `make check` runs
```

That compares the model with CRuby over CRuby's `bootstraptest` suite, over
every past disagreement in `corpus/regressions/`, and over the adversarial
programs in `corpus/tier3/`, and fails on any disagreement.
[How the model is tested](../docs/testing.md) describes what is compared and how
the recorded baseline works.

## Running it directly

```sh
uv sync                                                       # Python 3.12 or newer
uv run difftest run --tier 0 --sut lean                       # bootstraptest against the model
uv run difftest run --tier regressions --sut lean             # every past disagreement
uv run difftest replay corpus/tier3 --sut lean                # a saved corpus
uv run difftest run --tier 1 -n 300 --sut lean --seed 1       # 300 generated programs
uv run difftest run --tier 1 -n 300 --sut desugar --inject-bug  # self-test: must find disagreements
uv run pytest                                                 # this package's own tests
```

`--sut lean` needs the model built (`make run`). `DIFFTEST_RUBY` selects the
CRuby to compare against; the default is Homebrew's `ruby` if there is one, and
otherwise the `ruby` on your `PATH`.

Each run writes `cases.jsonl` (one record per program), `summary.json` and
`report.md` to its output directory (`--out`, default `reports/<timestamp>/`),
and exits with status 1 if anything disagreed.

## Where programs come from

| Tier | Source |
|---|---|
| 0 | CRuby's `bootstraptest` suite, about 1300 small self-contained programs |
| 1 | Random programs generated with Hypothesis. A disagreement is shrunk and saved to `corpus/regressions/` |
| 1.5 | Generated programs that probe evaluation order |
| 3 | Adversarial programs written to stress one feature each, in `corpus/tier3/` |
| 4 | Sorbet-annotated programs in `corpus/sorbet/`, for comparing Sorbet's static verdict with what the program does |
| `regressions` | Every disagreement found so far, minimized |

## Systems under test

| `--sut` | What runs |
|---|---|
| `lean` | The desugarer, then the `rubycore` executable |
| `desugar` | The desugarer, the result printed back as Ruby, then CRuby |
| `identity` | CRuby again; a smoke test of the harness that must always agree |
| `sig-strip` | The program with its Sorbet signatures removed |

A system under test can answer *unsupported*, with a reason, for a program
outside what it handles. Those are reported separately and are never counted as
agreement or as disagreement.

## Layout

| Path | Contents |
|---|---|
| `difftest/` | The engine: the runner, the comparison, the generators (`tiers/`), the systems under test (`sut.py`) |
| `ruby/` | Ruby helpers: the observation wrapper and the scripts that strip Sorbet annotations |
| `corpus/` | The saved programs described above |
| `coverage-baseline.json` | The recorded `bootstraptest` result that `make conformance` compares against |
| `tests/` | This package's unit tests |
