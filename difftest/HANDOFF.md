# difftest — hand-off note for the next session

> Written 2026-07-07 so a fresh-context agent can pick up the differential test
> engine without re-deriving anything. Read [`README.md`](README.md) first (how
> to run, the SUT contract), then this file (state, design decisions, next
> steps). Style follows the harness hand-off notes
> (`../harness/desugar-dt/M2-params-yield-plan.md`).

## Where things stand (resume point)

- **Branch:** `sam-xif-investigation`. Engine committed in `e4d2830`.
- **Run it:** `cd difftest && uv sync`, then the commands in README §Usage.
  Oracle is Homebrew CRuby 4.0.5 (auto-resolved; `DIFFTEST_RUBY` overrides).
  `ANTHROPIC_API_KEY` lives in the gitignored `.env` (loaded by the CLI; real
  env vars win).
- **Built and verified:**
  - Core pipeline: `CRubyRunner` control (prelude wrapper → `Observation` =
    stdout / result `inspect` / exception, normalized addresses, pinned hash
    seed, determinism double-run), verdicts, JSONL+Markdown reports, CLI
    (`run` / `gen3` / `replay`).
  - **Tier 1** (Hypothesis): scope-aware strategies over a surface AST
    (`tiers/tier1/`); campaign is a Hypothesis property asserting agreement, so
    disagreements shrink automatically → `corpus/regressions/`.
  - **Tier 3** (Anthropic API): per-category prompts + structured JSON output
    (`claude-opus-4-8`), validation gate (parse / terminate / deterministic
    double-run), persisted replayable corpus `corpus/tier3/`.
  - SUTs: `stub` (Lean placeholder), `identity` (smoke), `desugar` (adapter
    over `../harness/desugar-dt/`; `--inject-bug` = detection self-test).
  - Evidence: identity 200/200 agree; healthy desugar 150/150 agree (all
    in-fragment); injected `&&` bug found and minimized; tier-3 corpus (68
    cases, all 7 categories) replays 68/68 agree vs identity and 31 agree /
    37 gated / 0 disagree vs desugar. 38 pytest tests green.
  - **Tier 0** (conformance corpora): `sources.py` loads the harvested
    bootstraptest corpus (`run --tier 0`; N1–N5 in `implementation-notes.md`).
    Full-corpus baseline vs desugar: 751 agree / 544 unsupported / 9 excluded
    with reasons / **0 disagree** (`reports/tier0-desugar-full/`) — an
    independent cross-check of the harness's own 752/1299.
  - **Mixed campaigns** (`run --mix tier1=0.9,tier0=0.05,tier3=0.05`): built
    as HANDOFF resolution **(b)** — the campaign stays one Hypothesis property,
    arms chosen by a weighted integer draw (`campaign.py`, which subsumed
    `tiers/tier1/campaign.py`; N6–N8).
- **Stubs:** tier 2 (mutation of scraped Ruby) is a documented generator slot
  with no code. 2026-07-07 refocus decision: corpora that cover the language's
  real distribution (tier 0) and adversarial tail (tier 3, seeded by AI) come
  first; Superion-style subtree splicing is deferred and will use those
  corpora as its seed pool when built.

## Load-bearing design decisions (don't silently change)

1. **The SUT protocol is the decoupling point.** `run(source) ->
   Observation | Unsupported`. `Unsupported(reason)` is a *fragment gate*, not
   a failure — partial models are first-class. The Lean interpreter plugs in
   here; nothing else in the engine may know what the SUT is.
2. **Every exclusion carries a reason** (parse error, timeout,
   nondeterministic, out-of-fragment) — the project's "no silent caps" rule.
3. **Deterministic errors are valid oracle cases** (identical exceptions =
   agreement); we do not try to generate only "valid" programs.
4. **Termination by construction in tier 1:** loops exist only in bounded
   counter form, and loop counters are `frozen` in the generation `Env` (both
   plain and op-assign reassignment excluded — either can livelock the
   counter; nested loops must draw a *free* loop var, see
   `strategies.py`). Preserve these invariants when extending the AST.
5. **Tier-3 corpus is committed** (generation costs money; replay is free).
   The `.json` sidecar records category/description/model/response-id.
6. **Hypothesis is the tier-1 engine specifically for its shrinker** — any
   redesign of the campaign loop must keep a path to minimized reproducers.

## Mixed-tier campaigns: built (resolution b, as recommended)

`run --mix tier1=0.9,tier0=0.05,tier3=0.05` — implemented 2026-07-07 as the
Hypothesis-hosted mix: `campaign.py::run_generative_campaign` (which subsumed
`tiers/tier1/campaign.py`; `--tier 1` is the `mix={"tier1": 1.0}` special
case). Arm choice is a weighted `st.integers(0,999)` threshold draw
(implementation-notes N6–N8). Tier-1 disagreements shrink exactly as before;
a disagreeing corpus draw is reported as `campaign.disagreeing_corpus_case`.
Still open from the original sketch: a "delta-debug via CRuby" pass for
corpus-case disagreements (05-differential-testing §5), and weighting corpus
sampling toward never-yet-disagreeing cases (currently uniform).

## Other enhancement ideas (roughly ordered by value)

1. ~~**Tier-3 coverage**~~ **done 2026-07-07:** all seven categories populated
   (68 cases, ~10 each); only 2 rejects total, both `namespaces` programs
   probing dynamic constant assignment (a parse-time SyntaxError) — prompts
   look healthy.
2. **Grow the tier-1 vocabulary** toward the semantics core: method calls with
   splats, kwargs (mind the Ruby-3 separation trap — see
   `../harness/desugar-dt/M2-params-yield-plan.md`), classes + ivars +
   dispatch (`class`/`def`/`new`), `begin/ensure`, proc/lambda. Each new form
   must preserve the termination + scope invariants above.
3. **Generator-health metrics in the report:** parse rate, exclusion rate,
   mean program size, AST-node-kind histogram — cheap, makes vocabulary
   growth measurable.
4. **Tier 2 (mutation):** the tier-1 AST + renderer make Superion-style
   subtree splicing nearly free *for generated programs* (prong2-design §2
   option B); mutating *scraped* Ruby needs a Prism→surface-AST importer —
   bigger, design first.
5. **More tier-0 sources:** bootstraptest is in (see above); next candidates
   are `ruby/spec` (convert per-example assertions to prints) and AI-translated
   foreign suites (needs a provenance/licensing think first).
6. **Coverage-guided steering:** feed which AST-kind pairs have appeared in
   agreeing runs back into strategy weights (05 §7, "rule-pair coverage").
7. **Parallel oracle execution** (`ProcessPoolExecutor` around `run_case`) —
   oracle runs dominate wall-clock (~4 subprocess calls/case).
8. **Three-way triangulation** (TruffleRuby/JRuby as extra controls) for
   disagreement triage (05 §5) — only worth it once a real SUT disagrees.
9. **Heap projection in `obs`** (05 §3.1) — deferred until the Lean model
   makes ivar-level comparison meaningful.

## How this fits the overall plan

The engine is the standing realization of prongs 2+3 of
[`../docs/semantics/06-desugaring-and-its-testing.md`](../docs/semantics/06-desugaring-and-its-testing.md)
and the harness half of [`../docs/semantics/05-differential-testing.md`](../docs/semantics/05-differential-testing.md).
The sequence remains: grow the desugar fragment (next batch: **M2 params +
yield**, plan in `../harness/desugar-dt/M2-params-yield-plan.md`) → meet the
desugar exit criterion (06 §7) → build the Lean model (artifacts 01–02 →
`inductive Step` + fuel interpreter) → **wire it in as a SUT here** (claim C1
of 05 §1). The `desugar` SUT meanwhile gives the engine a real consumer: every
difftest campaign against it is extra validation of the front end, and its
`Unsupported` reasons are another next-blocker signal for fragment growth.
