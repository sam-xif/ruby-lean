# difftest — differential test engine for Ruby

A multi-tier engine that generates Ruby test programs, runs each under **CRuby
(the control)** and an arbitrary **system under test (SUT)** — eventually the
in-Lean semantics — and reports where they differ. Methodology per
[`../docs/semantics/05-differential-testing.md`](../docs/semantics/05-differential-testing.md);
tier-1 design realizes [`../harness/desugar-dt/prong2-design.md`](../harness/desugar-dt/prong2-design.md).
Picking this up fresh? Read [`HANDOFF.md`](HANDOFF.md).

## Setup

```sh
cd ruby/difftest
uv sync                 # Python 3.12+, hypothesis, anthropic
# oracle: Homebrew CRuby (auto-resolved); override with DIFFTEST_RUBY=/path/to/ruby
# tier 3 only: export ANTHROPIC_API_KEY=...
```

## Usage

```sh
uv run python -m difftest run --tier 1 -n 200 --sut identity --seed 42
uv run python -m difftest run --tier 1 -n 300 --sut desugar --inject-bug   # detection self-test
uv run python -m difftest run --tier 0 --sut desugar                       # bootstraptest corpus (all; -n samples)
uv run python -m difftest run --mix tier1=0.9,tier0=0.05,tier3=0.05 -n 200 --sut desugar
uv run python -m difftest gen3 --category eval-order -n 5                  # costs API tokens
uv run python -m difftest replay corpus/tier3 --sut identity
uv run pytest
```

Reports land in `reports/<timestamp>-<label>/` (gitignored): `cases.jsonl`
(one record per case: source, both observations, verdict, reason, timings),
`summary.json`, and a human `report.md`. Exit code 1 iff any DISAGREE.

## The tiers

| Tier | Source | Status |
|---|---|---|
| 0 | conformance corpora — first source: MRI's `bootstraptest`, harvested by the desugar harness (`difftest/sources.py`) | built |
| 1 | Hypothesis AST fuzzing (`difftest/tiers/tier1/`) | built |
| 2 | mutation of scraped real-world Ruby | **stub** — future generator slot |
| 3 | Anthropic-API-generated adversarial programs (`difftest/tiers/tier3/`) | built |

**Tier 0** replays MRI's own `bootstraptest` suite — ~1300 self-contained
single-file programs harvested by `../harness/desugar-dt/bin/harvest_bootstraptest`
(the corpus is not vendored; the source errors with the harvest recipe when it
is missing). No pre-filter: the run-time control gate excludes unusable cases
with reasons. This is the quick-initial-confidence corpus a new SUT meets first.

**Tier 1** generates a *surface* AST under scope-aware strategies (an
environment of bound locals/defined methods threads through generation, so
names resolve and dispatch fires; loops are bounded counters, so programs
terminate by construction). The campaign is a Hypothesis property asserting
agreement — any disagreement is **automatically shrunk** and the minimal
reproducer saved to `corpus/regressions/`.

**Tier 3** prompts Claude (default `claude-opus-4-8`, structured JSON output)
for adversarial programs per semantic category (dispatch, blocks/jumps,
eval-order, exceptions, namespaces, kwargs, metaprogramming — see
`tiers/tier3/prompts.py`). Every program passes a validation gate (parses,
terminates, deterministic under a double run) before entering
`corpus/tier3/<category>/NNN.rb` with a `.json` sidecar; rejects are logged
with reasons. The corpus is committed and replayed for free thereafter.

**Mixed campaigns** (`run --mix tier1=0.9,tier0=0.05,tier3=0.05`) sample each
case from a weighted arm: fresh tier-1 generation or a persisted corpus. The
campaign remains a single Hypothesis property, so tier-1 disagreements still
shrink to minimal reproducers; a disagreeing corpus draw is reported by its
corpus id instead (it is already small and persisted). Non-critical
implementation choices are recorded in
[`implementation-notes.md`](implementation-notes.md).

## What is compared (`Observation`)

`obs = (stdout, result_repr, exception[class, message])`, normalized on both
sides: `0x…` object addresses are rewritten to allocation-order indices,
`RUBY_HASH_SEED=0` is pinned. Identical deterministic *errors* count as
agreement. Programs that don't parse, time out, or are nondeterministic under
the control are excluded as `CONTROL_INVALID` — always with a reason, never
silently.

Known v1 wrapper limits (see `difftest/control.py`): writes to the `STDOUT`
constant bypass capture; heap projection is deferred.

## The SUT interface (how the Lean model plugs in)

```python
class SystemUnderTest(Protocol):
    name: str
    def run(self, source: str) -> Observation | Unsupported: ...
```

`Unsupported(reason)` is the fragment gate — a SUT that models a subset
declares out-of-fragment programs instead of failing on them. Built-in SUTs:

- `stub` — supports nothing; the original placeholder.
- `identity` — CRuby again; pipeline smoke test (must be 100% AGREE).
- `desugar` — adapter over `../harness/desugar-dt/` (desugar → render → CRuby);
  with `--inject-bug` its known-buggy `&&`/`||` desugar produces real
  disagreements, which is the engine's end-to-end detection self-test.
- `lean` — **the Lean model** (`../lean/`): desugar → RubyCore JSON →
  `rubycore` binary (build it first: `cd ../lean && lake build`). Composes
  two fragment gates (desugar's and the model's L0); binary exit 3 =
  Unsupported, exit 1 = model bug (surfaced as `MODEL-BUG:` reasons, never
  silently).

## Deferred (deliberately)

Tier 0/2 generators; heap projection in `obs`; three-way triangulation
(TruffleRuby/JRuby); coverage-guided generation steering; Batches API bulk
tier-3 generation; parallel oracle execution.
