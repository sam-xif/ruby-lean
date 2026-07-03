# Fragment-Expansion Strategy — driving `desugar` toward full bootstraptest coverage

> How we iteratively grow the fragment `desugar` handles, using the harvested MRI
> `bootstraptest/` corpus (prong 1) as the coverage target. Data-driven: expansion is
> prioritized by measured blocker impact, not guesswork.
>
> References: `../../docs/semantics/06-desugaring-and-its-testing.md` (§4 corpus, §5
> coverage, §7 exit criterion), `PROCEDURE-authoring-semantics.md`, `implementation-choices.md`.

## 1. Reframe the target: "100% of the *in-scope* subset"

Literal 100% of bootstraptest is neither achievable nor desirable: the suite deliberately
exercises VM internals (`eval` of strings, threads/`Ractor`/GC, `ObjectSpace`, backtick
shell-out, flip-flops, `__method__`/backrefs) that are **out of scope by design**
(PROJECT_PLAN §4, artifact 00 §6). So the target is:

```
  coverage  =  (in-fragment AND round-trip-agree)  /  (harvested_total − explicitly_out_of_scope)
```

and the job is to drive that to 100% while keeping `explicitly_out_of_scope` a **small,
enumerated, justified list** — no silent caps (PROJECT_PLAN principle). Two invariants:

- **"In-fragment" is not the goal — "in-fragment AND agree" is.** Every newly-admitted
  program must also pass the round-trip. Expect some to *disagree* on admission: that's
  the payoff — a real `desugar`/`render` bug the fragment growth exposed.
- **The out-of-scope list is a deliverable**, updated in `implementation-choices.md` with
  a one-line justification per entry.

## 2. Measurement comes first (make it a harness command)

Expansion is a measure → expand → re-measure loop, so the measurement must be cheap and
first-class. Add a `bin/coverage` tool (design below) reporting three things over any
corpus:

1. **Fragment coverage** — `in-fragment / (total − excluded)` and `agree / in-fragment`.
2. **Blocker histogram** — for each unsupported Prism node type, the number of programs it
   blocks (full profile: *all* blockers per program, not just the first `desugar` trips
   on — the first-blocker view undercounts because one program has several).
3. **Coverage ratchet** — a committed baseline number that may only go **up**; a
   regression fails. This turns "grow the fragment" into a monotone, reviewable metric.

Re-measure after *every* expansion: the blocker distribution shifts as programs unlock to
their next blocker.

> Note: the node-type walk used for planning (below) is an *optimistic* approximation — it
> ignores the "simple params only" and "eval-string" gates, so it slightly over-counts.
> The real number comes from running `desugar` + the round-trip.

## 3. Current blocker data (harvested corpus, 1299 parseable programs)

Baseline: **239/1299 (18.4%)** fully in-fragment by node-type (214 actually agree today).
No single silver bullet — the coverage curve is smooth:

| add top-N unsupported node types (by frequency) | programs fully in-fragment |
|---|---|
| 0 (baseline) | 18.4% |
| 15 | 50.5% |
| 30 | 76.7% |
| ~75 (all) | 100% |

Highest-impact blockers (programs affected): `constant_read` (480), `class` (301),
`begin`/`rescue`/`ensure` (171/147/49), method params — `rest` (137) / `optional` (106) /
`block` (95) / `forwarding` (31), `splat` (122), globals (92+73), `yield` (73), hashes
(`assoc` 73 / `keyword_hash` 62 / `hash` 35), multi-assign (`local_variable_target` 94 /
`multi_write` 69), `break`/`return` (58+42), `forwarding_super` (56), `range` (48),
op-assign (`local_variable_operator_write` 47), `defined?` (38), `case`/`when` (30/30),
ivars (34+29).

## 4. Classify every feature: desugaring vs new core node vs out-of-scope

Where the work goes differs by kind (and this anticipates the Lean model):

- **DESUGARING** — a rewrite into existing/near-core forms; **no new RubyCore node**, just
  a rule (+ track in `Desugar::RULES`). Examples: `case/when → if/===` chain,
  `for → each`+block, multiple-assignment, op-assign (`+=`, `x[i] += e`, `a.b += e`),
  splat in calls (partly). These carry evaluation-order obligations → each needs an
  adversarial trace seed.
- **NEW CORE NODE** — a genuine RubyCore form needing `render_core` + `is_core` now, and a
  `Step` rule *later* (it's part of the model, not sugar). Examples: `class`/`module`,
  singleton class/def (eigenclass), `def` with full params, constants, globals, ivars,
  cvars, `begin`/`rescue`/`ensure`, `yield`, `return`/`break`/`next`, numeric literals
  (`float`/`rational`/`imaginary`), `hash`, `range`, `super`, `alias`, `undef`.
- **OUT OF SCOPE** — add to the exclusion list with justification, never covered. Examples:
  `eval`-string (22 programs), backtick/`x_string` (shell-out), flip-flop,
  `source_line`/back-references, and anything the harvester already drops (threads, GC,
  `ObjectSpace`, `require`).

Keeping this split explicit tells us (a) how much is cheap rewrite vs. real modeling, and
(b) exactly which new nodes the eventual Lean `Step` relation must cover.

## 5. The expansion plan — batches by dependency cluster (with measured unlock)

Batch by *cluster* (features that jointly unlock programs), not strict single-feature
frequency: a class-defining program needs constants + params + ivars + `begin` all at
once, which is why constants alone (in 480 programs) don't unlock them alone. Cumulative
coverage, measured:

| Milestone | Adds | Kind | Cumulative coverage |
|-----------|------|------|---------------------|
| **baseline** | — | — | **18.4%** |
| **M1 · values & statements** | constants (read/write/path), globals, ivars, cvars, `float`/`rational`/`imaginary`, `range`, `hash`/`assoc`/`keyword_hash`, op-assign (all targets), multiple-assignment (`*_target`/`multi_write`), `splat`, `return`/`break`/`next` | mostly new core nodes + a few desugarings (op-assign, multi-assign) | **41.9%** |
| **M2 · methods & blocks (full)** | all param kinds (`optional`/`rest`/`keyword`/`block`/`forwarding`), `forwarding_super`, `yield` | core nodes | **55.2%** |
| **M3 · classes & exceptions** | `class`, `module`, singleton class, `begin`/`rescue`/`ensure`, constant-path write | core nodes | **83.8%** ← biggest jump |
| **M4 · control & sugar** | `case`/`when` (+`case/in`), `for`, `defined?`, `regexp`, symbol-interp, `retry`/`redo` | desugarings + core | **92.5%** |
| **M5 · long-tail triage** | `forwarding_arguments` (27), `alias`/`super`/`undef` (15/14/7), rescue-modifier (9), `index` op-write (5), numbered params (4), flip-flop (3), backtick (2), … | mix; several → out-of-scope | **→ ~98–100% of in-scope** |

Order rationale: M1 is self-contained (no class/def machinery) and unlocks +24 points
immediately; M2 completes method/block shapes M3 depends on; **M3 (classes) is the single
biggest unlock** because bootstraptest is class-heavy; M4 mops up control-flow sugar; M5
triages the ~97-program tail, moving each remainder to either a rule or the enumerated
out-of-scope list.

## 6. The per-feature iteration loop

For each feature in the current batch (following `PROCEDURE-authoring-semantics.md`):

1. **Classify** (§4): desugaring / new core node / out-of-scope.
2. **Implement**
   - *desugaring* → add the rewrite in `lib/desugar.rb`, register the rule in
     `Desugar::RULES`;
   - *core node* → add to `RubyCore::HEADS` + `explain`, a `render_core` case, and the
     `desugar` mapping;
   - *out-of-scope* → raise `Unsupported` with a clear reason and add the entry to the
     exclusion list in `implementation-choices.md`.
3. **Seed it.** Add a self-contained seed exercising the feature. If it carries an
   **evaluation-order / once-only obligation** (op-assign receiver-once, multi-assign
   order, `case` subject-once + `===` order, `for` variable leak, splat evaluation), add a
   **trace-augmented adversarial seed** (artifact 06 §2) — value-only checks miss these.
4. **Keep the round-trip green** (`bin/run`): fix any disagreement (that's a found bug), or
   record a genuine out-of-scope skip.
5. **Re-measure** (`bin/coverage`), ratchet the baseline up, **commit** (+ an
   `implementation-choices.md` entry for any scope decision, per the rollback convention).

## 7. Guardrails

- **Ratchet:** coverage is monotone; a drop fails. Prevents silent regressions as the
  fragment churns.
- **No silent caps:** every not-covered program is either a tracked bug, a pending batch
  item, or an enumerated+justified out-of-scope entry.
- **Adversarial seed per obligation:** structural admission isn't enough; the ordering
  sugars must be trace-tested.
- **Desugar ≠ semantics:** admitting a *core node* here needs only `render_core`/`is_core`
  (no `Step` rule yet) — but tag it as "structural core" so the eventual Lean model knows
  it owes a rule. Pure desugarings owe nothing to the model.
- **Batch, then re-measure:** never plan more than one batch ahead on stale numbers.

## 8. Realistic end state

M1–M4 reach ~92% by the planning estimate; M5 triage pushes the *in-scope* fraction to
~100%, with a residual out-of-scope list on the order of a few dozen programs
(eval-string, backtick, flip-flop, VM-internal specials). The honest headline will be
"**100% of in-scope bootstraptest, N programs explicitly excluded (listed)**," not a bare
"100%".

## 9. Open questions

- **[?]** Should `bin/coverage` compute the full per-program blocker *set* (for batch
  planning) every run, or just the histogram (cheaper)? Full set is more useful but O(nodes).
- **[?]** `case/in` pattern matching (Ruby 3+) is a large sub-language — one batch, or its
  own fragment milestone with its own desugaring artifact?
- **[?]** Some "core nodes" (globals `$~`/`$1`, `defined?`) are semantically special
  (artifact 03 §6–§7); do we admit them structurally now and defer their semantics, or
  hold them out until the model is ready?
