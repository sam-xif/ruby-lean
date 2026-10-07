# scripts/ci/ — the CI harness

The workflow that runs these is [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml).
CI calls the repository's own documented commands (`scripts/reproduce.sh`,
`books/scripts/run_typed_ratchet.sh`, `desugar/bin/run`, …) rather than re-implementing them, so
local and CI semantics cannot drift.

## The three ratchets

A change can build cleanly and still silently regress a ratchet. Each ratchet has a
**checked-in high-watermark**, and CI fails if the live value falls below it. A rise is
progress: raise the watermark in the same PR to lock it in. The harness never lowers a
watermark — the only way it changes is a reviewed commit that edits the value.

| Ratchet | Metric | Watermark | Where | Owner in CI |
|---|---|---|---|---|
| Semantics bootstraptest | `agree`, `sut_unsupported`, `disagree` = 0 | minimum / maximum / zero | `difftest/coverage-baseline.json` | `check_semantics_watermark.sh` |
| Desugarer bootstraptest | `in_fragment`, `parseable` | minimum | `desugar/coverage-baseline.json` | `ruby desugar/bin/coverage` |
| Typed ratchet | `fragmentFloor`, `clinkFloor`, `safeRungFloor` + reach | minimum | `books/Books/TypeSoundness/Report/Active.lean` (the full-profile floors are in `books/Unrebuilt/SemLadder.lean`) | `books/scripts/run_typed_ratchet.sh` |

## `check_semantics_watermark.sh`

Reads a tier-0 `difftest` `summary.json` (the model replayed against MRI's
`bootstraptest`) and compares it to `difftest/coverage-baseline.json`:

```sh
# in a difftest run output directory containing summary.json
scripts/ci/check_semantics_watermark.sh /path/to/report

# intentionally record the current numbers as the new baseline (a reviewed commit)
scripts/ci/check_semantics_watermark.sh --save /path/to/report
```

- `agree < baseline` → **REGRESSION** (the model agrees on fewer programs)
- `sut_unsupported > baseline` → **REGRESSION** (the model's coverage shrank)
- `disagree > 0` → **REGRESSION** (a hard zero, not a watermark)
- `ran` differs → a note asking the baseline to move in the same PR

## `harvest_bootstraptest.sh`

One-shot sparse clone of `ruby/ruby` plus the harvester, for the tier-0 run. Idempotent;
honors `$RUBY_SRC` (default `/tmp/ruby-src`). CI caches the checkout and the harvested
corpus.
