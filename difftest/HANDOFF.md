# difftest — hand-off note for the next session

> Written 2026-07-07 so a fresh-context agent can pick up the differential test
> engine without re-deriving anything. Read [`README.md`](README.md) first (how
> to run, the SUT contract), then this file (state, design decisions, next
> steps). Style follows the harness hand-off notes
> (`../harness/desugar-dt/M2-params-yield-plan.md`).

## Where things stand (resume point)

- **Branch:** `sam-xif-investigation`. Engine committed in `e4d2830`.
- **Run it:** `cd ruby/difftest && uv sync`, then the commands in README §Usage.
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
    in-fragment); injected `&&` bug found and minimized; tier-3 `eval-order`
    batch 5/5 through the gate (vs desugar: 3 agree, 2 cleanly gated
    out-of-fragment). 23 pytest tests green.
- **Stubs:** tier 0 (AI-translated conformance suites) and tier 2 (mutation of
  scraped Ruby) are documented generator slots with no code.

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

## Requested next feature: mixed-tier campaigns

Sam wants campaigns that sample across tiers with configurable weights — e.g.
each case drawn 99/100 from tier 1, 1/100 from tier 3 (`--mix
tier1=0.99,tier3=0.01`). Design sketch:

- Introduce a `CaseSource` abstraction: something that yields the *next*
  `TestCase` on demand. Tier 3's source samples the persisted corpus
  (uniformly, or weighted toward never-yet-disagreeing cases); tier 1's source
  draws a fresh program from the strategies.
- The mixed campaign is then an ordinary iterator loop (like `replay`): seed a
  `random.Random`, pick a source per step by weight, run, record. Provenance
  already carries the tier per case, so reporting works unchanged.
- **The tension is shrinking.** The current tier-1 campaign gets minimization
  by living *inside* a Hypothesis property; an iterator-style mixed loop
  can't. Two viable resolutions (pick during implementation, record the choice
  in this file):
  a. **Post-hoc shrink pass:** when the mixed loop hits a tier-1 disagreement,
     re-enter a dedicated Hypothesis property seeded to regenerate that case
     (reuse the recorded seed + draw index) and shrink from there.
     Con: re-finding the case via seed replay needs care.
  b. **Hypothesis-hosted mix:** keep the campaign a Hypothesis property whose
     strategy is `st.one_of` weighted between `programs()` and
     `st.sampled_from(corpus_cases)` (weights via `st.integers(0,99)`
     threshold). Shrinking keeps working for tier-1 draws for free;
     corpus draws shrink only across corpus choice, which is fine.
     **This is the recommended shape** — it's ~30 lines in
     `tiers/tier1/campaign.py` generalized to `campaign.py`.
- Tier-3 cases found disagreeing don't need shrinking (they're small and
  hand-inspectable), but consider a follow-up "delta-debug via CRuby" pass
  later (05-differential-testing §5).

## Other enhancement ideas (roughly ordered by value)

1. **Tier-3 coverage:** generate batches for the six remaining categories
   (`gen3 --category all -n 10`); inspect rejects — the reject rate per
   category is itself signal about the prompts.
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
5. **Tier 0 (translated conformance suites):** pick a source suite (e.g.
   test262-style single-file cases), AI-translate to Ruby, validation-gate
   like tier 3. Needs a provenance/licensing think first.
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
