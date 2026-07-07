# difftest — implementation notes (non-critical choices, for rollback)

Same convention as the harness's `../harness/desugar-dt/implementation-choices.md`:
every non-obvious implementation choice gets a numbered entry here and this file is
committed on each change, so any decision can be found and reverted. Load-bearing
*design* decisions live in [`HANDOFF.md`](HANDOFF.md); these are the smaller calls.

## N1 — Tier 0 is repurposed as the conformance-corpus tier; bootstraptest is its first source

Tier 0 was originally sketched as "conformance suites from other languages,
AI-translated to Ruby". MRI's own `bootstraptest/` is a strictly cheaper first
occupant: already Ruby, already self-contained single-file programs, harvester
already exists (`../harness/desugar-dt/bin/harvest_bootstraptest`), no
translation or licensing questions. Translated foreign suites remain a future
tier-0 source, not a separate tier. (Refocus decision of 2026-07-07: corpora
covering the language's real distribution come before splicing/mutation.)

## N2 — Tier 0 has no pre-filter gate; the run-time control gate is the gate

Bootstraptest cases go straight into `run_case`, whose existing control gate
(parse check, timeout, determinism double-run) excludes unusable cases as
`CONTROL_INVALID` *with reasons* — consistent with "no silent caps" and with
the fact that the harvester already skips obviously out-of-scope files
(threads, `require`, `rand`, …). No separate validation pass to maintain.

## N3 — `run --tier 0` runs the whole corpus by default; `-n` takes a seeded random sample

`-n` therefore no longer has a global default of 100 in the CLI; tier 1
defaults to 100 when `-n` is omitted, tier 0 to "all". The sample is drawn
with `random.Random(seed)` and re-sorted by case id so reports stay in stable
order.

## N4 — The bootstraptest corpus stays unvendored (gitignored in the harness)

The difftest source points at the harness's harvested copy
(`../harness/desugar-dt/corpus/bootstraptest/`) and raises with the harvest
recipe when it is missing, rather than vendoring ~1300 upstream-derived files
into this repo.

## N5 — `manifest.json` rides along as provenance only

The harvester's per-case `expected` value is recorded in `TestCase.provenance`
for triage, but the differential verdict never uses it — the control (CRuby)
recomputes ground truth, which also keeps cases whose harvested `expected` was
approximate from producing false disagreements.

## N6 — Mixed campaigns live in `difftest/campaign.py`; the old tier-1 campaign module is subsumed

Per HANDOFF resolution (b): the campaign stays a Hypothesis property; the mix
is a strategy-level weighted choice between arms ("tier1" = fresh generation,
"tier0"/"tier3" = `st.sampled_from` a loaded corpus). `run --tier 1` is now
the `mix={"tier1": 1.0}` special case of `run_generative_campaign`;
`tiers/tier1/campaign.py` was deleted. The summary key changed from `"tier1"`
to `"campaign"` (now also carrying `mix` and `arm_counts`).

## N7 — Mix weights are quantized to thousandths; every arm gets ≥ 1 slot

The arm choice is `st.integers(0, 999)` against cumulative thresholds. Any
positive weight is rounded up to at least 1/1000 so a requested arm is never
silently dead (rounding drift is absorbed by the heaviest arm). A pure-tier-1
mix skips the arm-choice draw entirely, keeping shrink behavior and case ids
(`tier1-NNNNN`) identical to the old tier-1 campaign.

## N8 — Corpus draws in a mix get fresh `mix-NNNNN` ids; disagreements point back at the corpus

A corpus case can be drawn more than once per campaign, so each draw gets its
own case id with the original id in `provenance.corpus_id`. A disagreeing
corpus draw is reported as `campaign.disagreeing_corpus_case` and no
minimized-reproducer file is written (the case is already persisted and
small); only tier-1-origin disagreements land in `corpus/regressions/`.

## N9 — Mix weights are targets, not guarantees

Hypothesis draws integers non-uniformly (it biases toward shrink-friendly
values), so realized arm frequencies drift from the requested weights toward
the *first* arm in the mix spec — e.g. a requested 0.90/0.05/0.05 realized as
194/5/1 over 200 draws. This is accepted: the campaign's job is to interleave
sources, not to hit exact proportions, and the realized mix is always reported
as `campaign.arm_counts` in the summary. Write the heaviest arm first in
`--mix` so the bias reinforces rather than fights the intent. Revisit with an
explicitly seeded `random.Random` arm choice if exact proportions ever matter
(at the cost of the arm choice being invisible to the shrinker).

## N10 — Every control run executes in a fresh temp cwd

Discovered by the first full tier-0 run: bootstraptest cases create files in
the working directory (`zzz2.rb`, `b/foo`), littering the repo and letting
filesystem state leak between the determinism double-run and across cases.
`CRubyRunner.run` now runs each subprocess in its own
`tempfile.TemporaryDirectory`. The desugar SUT's *desugar* subprocess still
inherits the engine cwd (it only parses/rewrites, never runs the program);
the rendered program itself goes through `CRubyRunner.run` and is isolated.
