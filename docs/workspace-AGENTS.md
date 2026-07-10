# AGENTS.md — ruby investigation

Index and current state for the **Ruby-in-Lean semantics** investigation — one of two
sibling target investigations under the `sam-xif` workspace (the other is
[`../posix/`](../posix/AGENTS.md)). Start at the workspace umbrella
[`../AGENTS.md`](../AGENTS.md) for the shared framing artifacts (user stories,
bounded-effect-checking, language↔substrate relation) and how the two targets fit together.
This file is the Ruby map: skim it, then open the file you need. Keep it updated as the
project grows (it is a directory, not a place to duplicate content — link instead).

## What this project is

Building toward a **mechanized, executable semantics of Ruby in Lean 4**, with Ruby on
Rails as the flagship framework case study, validated by **differential testing** against
CRuby. See [`PROJECT_PLAN.md`](PROJECT_PLAN.md) for the full motivation, statistics,
prior-art survey, model sketch, and phased roadmap.

Two load-bearing ideas a new agent must internalize before touching anything:

1. **Everything is a message send; classes are ordinary heap objects.** So one dispatch
   rule carries the language and every metaprogramming feature reduces to *heap mutation*,
   not a new evaluation rule. Prefer "desugar + heap mutation" over adding rules.
2. **Build trust bottom-up, front end first.** We are validating
   `desugar : Surface → RubyCore` *before* giving RubyCore any semantics — its oracle is
   a round-trip through CRuby and needs no interpreter. See
   [`docs/semantics/06-desugaring-and-its-testing.md`](docs/semantics/06-desugaring-and-its-testing.md).

## Status (current phase)

- **Design artifacts (00–06): drafted.** Quasi-formal small-step semantics of the core,
  the differential-testing methodology, and the desugar-first plan.
- **Desugar harness: built and passing, fragment growing.** Validated on hand-written
  seeds + harvested `bootstraptest` on CRuby 4.0.5. **M1 done (minus splat):** variable
  namespaces, float, range/rational/imaginary→sends, op-assign, ||=/&&=, hash,
  return/break/next, multiple-assignment, **splat** (call args, array literals, rest
  params, massign rest-target + splat-RHS), + a **linearization pass** (hoists control-flow
  jumps out of operand position, e.g. `"#{next}"`). **M3 done (object-model core):**
  `class`/`module`/singleton-class, singleton `def self.m`/`def o.m`,
  `begin`/`rescue`/`else`/`ensure`, `retry`, `super`/bare-`super` — kept as keyword-rendered
  heads (not desugared to `Class.new`, which would change the lexical cref/self). Admitting
  these also surfaced + fixed three latent bugs (interp uses `String(e)` not `to_s`;
  assignment-call `a[i]=v` value is the RHS; do-while `begin…end while` gated) → **752/1299
  bootstraptest agree, 0 disagree, 0 harness-error**. `bin/coverage` tracks a ratchet
  (baseline 752). Deferred: single-RHS massign (to_ary), `const`/`@@x` `||=` (need
  `defined?`), indexed/attr **op**-assign, double-splat `**`/kwargs, block-pass `&blk`,
  `...` forwarding, constant paths `A::B`, do-while, `super` arg-forwarding subtleties.
- **Lean model: L0 implemented and difftesting** ([`lean/`](lean/README.md), per the
  sketch [`docs/semantics/lean-model-sketch.md`](docs/semantics/lean-model-sketch.md)):
  small-step machine (kont stack + frame store), fuel interpreter, Ruby-faithful
  repr/error-message layer, oracle-generated CRuby name tables for dispatch fidelity
  (unmodeled builtins gate as `Unsupported` instead of mis-dispatching), and the SUT
  executable wired into the difftest engine as `--sut lean` (source → desugar →
  RubyCore JSON → Lean → Observation). **Baseline (2026-07-07): full bootstraptest
  295/1304 agree, 0 disagree** (rest gated Unsupported: 544 upstream desugar, then
  class defs L2 / blocks L1 / unmodeled methods+constants); tier-1 fuzzing already
  caught and fixed one real bug (coercion-error messages use inspect for special
  constants, class name otherwise). The `inductive Step` relation (definition of
  record) is not yet authored — interpreter came first to meet the engine on day one.
- **Not started:** the `Step` relation + adequacy theorems; artifacts 07–10 (param
  binding, core library, metaprogramming, Rails slice).

## Directory index

> Shared framing artifacts (`user-stories.md`, `bounded-effect-checking.md`,
> `relating-language-and-substrate.md`) and the sibling `posix/` investigation live one
> level up — see the workspace umbrella [`../AGENTS.md`](../AGENTS.md). Everything below is
> the Ruby investigation.

### `PROJECT_PLAN.md`
The master plan: why Ruby+Rails, usage statistics, honest prior-art survey (Essence of
Ruby, RIL, KJS/JSCert), the dual interpreter+relation Lean design, differential-testing
strategy, phased roadmap, risks.

### `docs/semantics/` — quasi-formal semantics (the spec we intend to mechanize)
Start at [`docs/semantics/README.md`](docs/semantics/README.md) (reading order + conventions).

| File | Covers |
|------|--------|
| `00-notation-and-syntax.md` | machine config `⟨K,H,Ξ⟩`, frames, judgments, RubyCore grammar, **desugaring table (§5)**, observation function |
| `01-object-model.md` | values/heap, classes as objects, eigenclasses, identity, truthiness, freeze |
| `02-dispatch-and-mro.md` | ancestor chain, lookup, send, `method_missing`, `super`, visibility |
| `03-variables-scope-constants.md` | 5 namespaces, local/block scope, class vars, two-phase constant lookup |
| `04-blocks-procs-control-flow.md` | closures, proc-vs-lambda, `yield`, `return`/`break`/`next`/`redo`/`retry`, exceptions/`ensure` |
| `05-differential-testing.md` | oracle harness, `obs` normalization, test sources, generation, triage, rule-coverage metric |
| `06-desugaring-and-its-testing.md` | the desugar-first plan: round-trip oracle, eval-order trace, three-pronged corpus, exit criterion |
| `PROCEDURE-authoring-semantics.md` | **agent playbook** for authoring/extending these artifacts against a Ruby oracle |
| `linearization.md` | worked example of nontrivial desugaring: hoisting control-flow jumps out of operand position (`"#{next}"`) |
| `co-semantics.md` | **framing (early draft, to grow):** Ruby + Rails as a *pair* of semantics at two altitudes joined by a refinement/bisimulation correspondence — structural `α` where macros define methods, observational `α` where `method_missing` does not; correspondences testable via `obs⁺` before the Lean model exists. §5: proof-goal shape (coupling invariant `Inv`, stuttering forward simulation — same machinery as `relating-language-and-substrate.md` — `escape` event for invariant-breaking programs, miniRails not real Rails in the proof). §6: everything hinges on `Inv` — clause taxonomy + validate it as an executable heap predicate against CRuby first |

Evidence tags used throughout: **[V]** verified against CRuby, **[D]** from docs/ISO 30170,
**[?]** open question for differential testing.

### `harness/desugar-dt/` — the differential-testing harness (runnable)
Ruby + Prism prototype validating `desugar` against CRuby. See its own
[`README.md`](harness/desugar-dt/README.md) to run it, and
[`implementation-choices.md`](harness/desugar-dt/implementation-choices.md) for every
non-critical decision (C1–C11) — **committed on each change for rollback**.

| Path | Role |
|------|------|
| `lib/rubycore.rb` | RubyCore node set (S-expr) + `is_core?` |
| `lib/desugar.rb`  | `Prism AST → RubyCore` + per-rule coverage |
| `lib/render.rb`   | `RubyCore → Ruby` (re-parseable) |
| `lib/observe.rb`  | `obs⁺` via CRuby subprocess (stdout = eval-order trace) |
| `lib/roundtrip.rb`| round-trip + `is_core` + normal-form + triage |
| `bin/run`         | corpus driver; agreement + coverage report |
| `bin/harvest_bootstraptest` | prong-1 corpus harvester (output gitignored) |
| `corpus/seeds/`   | self-contained seeds incl. eval-order adversarial cases |

### `difftest/` — the multi-tier differential test engine (Python, runnable)
Standing engine that generates Ruby programs and compares **CRuby (control)** against an
arbitrary **SUT** (`Observation | Unsupported` protocol — the future Lean interpreter plugs
in here; deliberately decoupled from any modeling approach). Built: **tier 0**
(conformance corpora — harvested bootstraptest replay; full-corpus baseline vs desugar:
751 agree / 0 disagree), **tier 1** (Hypothesis scope-aware AST fuzzing with automatic
shrinking of disagreements → `corpus/regressions/`), **tier 3** (Anthropic-API-generated
adversarial programs, all 7 semantic categories, validation-gated into the committed
`corpus/tier3/`), and **mixed campaigns** (`run --mix tier1=0.9,tier0=0.05,tier3=0.05`,
Hypothesis-hosted so shrinking survives). Tier 2 (mutating scraped Ruby) is a stub slot,
deliberately deferred until the corpora exist to seed it. Built-in SUTs: `stub`,
`identity` (smoke test), `desugar` (adapter over `harness/desugar-dt/`; `--inject-bug` is
the detection self-test). See [`difftest/README.md`](difftest/README.md) to run it,
[`difftest/HANDOFF.md`](difftest/HANDOFF.md) for the fresh-context hand-off (state,
load-bearing invariants, enhancement queue), and
[`difftest/implementation-notes.md`](difftest/implementation-notes.md) for non-critical
implementation choices (N1–N8, committed for rollback).

### `lean/` — the Lean 4 model (runnable SUT)
The mechanization of artifacts 00–04 begun from the sketch. See
[`lean/README.md`](lean/README.md) for layout, build (`lake build`, toolchain pinned),
the L0 fragment inventory, and the two fidelity policies (three-way lookup-miss split;
`reprPure` gating); [`lean/HANDOFF.md`](lean/HANDOFF.md) for the fresh-context hand-off
(state, coverage assessment — 22/29 heads, 295/760 in-desugar-fragment bootstraptest
cases, 0 disagree — and the ordered next steps: desugar M2 → L1 blocks → L2 classes →
`inductive Step`); [`lean/implementation-notes.md`](lean/implementation-notes.md) for
revertable decisions (L1–L12). `RubyCore/CRubyNames.lean` is **generated** by
`lean/scripts/gen_cruby_names.rb` against the pinned oracle. The harness↔Lean interface
is `harness/desugar-dt/lib/export.rb` (versioned RubyCore JSON; `bin/export-json`).

### `ruby_papers/` — reference PDFs
`essence_of_ruby.pdf` (Ueno et al., APLAS'14 — closest prior semantics), `ruby_intermediate_language.pdf`
(Furr et al., DLS'09 — RIL/desugaring reference), `csmith.pdf` (PLDI'11 — differential
testing), `superion.pdf` (ICSE'19 — grammar-aware fuzzing).

### Repo root (outside this workspace)
`../../docs/2026-06-30-initial-plan.md` is the team's original brainstorm (Mike/Sam/Callan);
root `README.md`/`.gitignore` are the base repo.

## Conventions

- **Semantics style:** small-step SOS over the explicit config in artifact 00; the
  inductive relation — not the interpreter — is the definition of record (PROJECT_PLAN §7).
- **When authoring a semantics artifact:** follow `PROCEDURE-authoring-semantics.md` —
  scope one domain, read docs (`[D]`), interrogate the CRuby oracle with minimal
  discriminating snippets (`[V]`), leave `[?]` for differential testing, update the
  `docs/semantics/README.md` index.
- **When extending `desugar`:** add a rule + track it in `Desugar::RULES`, add a seed that
  exercises it (and an eval-order adversarial seed if it has a once-only/ordering
  obligation), keep the round-trip green (`bin/run`).
- **Decisions:** record non-critical harness choices in `implementation-choices.md` and
  **commit that file** so any decision is revertable.

## Environment

- Oracle: **CRuby 4.0.5** installed via Homebrew (`$(brew --prefix ruby)/bin/ruby`, has
  `+PRISM`). System Ruby 2.6 is too old. RVM failed to compile (deprecated `openssl@1.1`).
- Run the harness: `RUBY=$(brew --prefix ruby)/bin/ruby; $RUBY sam-xif/ruby/harness/desugar-dt/bin/run`.
- `bootstraptest/` corpus is harvested on demand (not vendored); recipe in the harvester header.

## Git

- Work happens on branch **`sam-xif-investigation`** (based on `origin/main`).
- Commit messages end with the project's `Co-Authored-By` trailer. Commit/push when asked.

## Open threads / next steps

- Grow the desugar fragment toward full bootstraptest coverage per the data-driven plan
  in [`harness/desugar-dt/fragment-expansion-strategy.md`](harness/desugar-dt/fragment-expansion-strategy.md)
  (batches M1–M5). **Current: 752/1299 bootstraptest agree, 0 disagree** (M1 + splat + M3
  object-model core done — see implementation-choices C12–C20; the M3 plan
  [`harness/desugar-dt/M3-classes-plan.md`](harness/desugar-dt/M3-classes-plan.md) is now
  largely realized). **Next: M2 params + `yield`** — the fresh `bin/coverage --full`
  next-blocker histogram is unambiguous: `optional_parameter_node` (106),
  `block_parameter_node` (95), keyword params, and `yield_node` (73) now dominate, since
  admitting classes exposed the method bodies inside them. Then `case`/`when` (30),
  constant paths `A::B` (41), `defined?` (38). A detailed fresh-context hand-off plan for M2
  is in [`harness/desugar-dt/M2-params-yield-plan.md`](harness/desugar-dt/M2-params-yield-plan.md)
  (the central call: migrate the `def`/`block`/`defs` param slot from a flat `[String]` to a
  structured param-node list; `yield` as a head; the Ruby-3 keyword/positional-hash
  separation trap; eval-order adversarial seeds for lazy defaults; land in two commits).
- Prong 2/3 are now realized as the standing **`difftest/` engine** (Python; tier 1 =
  Hypothesis scope-aware fuzzing per [`harness/desugar-dt/prong2-design.md`](harness/desugar-dt/prong2-design.md),
  tier 3 = AI-generated adversarial corpus). Grow it: more tier-1 vocabulary (classes,
  splats, kwargs), tier-3 corpus across all categories, tiers 0/2, and eventually the Lean
  interpreter as a SUT. Verified end-to-end: identity SUT 200/200 agree; desugar SUT with
  `DESUGAR_BUG=1` yields a shrunk minimal disagreement.
- **Lean model (begun; `lean/`):** grow the L0 fragment along the difftest
  `Unsupported`-reason histogram (same ratchet discipline as the desugar: 0 disagree,
  agreement only goes up — baseline 295). Ordered plan in
  [`lean/HANDOFF.md`](lean/HANDOFF.md): desugar M2 (biggest lever, 544 cases gate
  upstream) → L1 blocks/`yield` → L2 class forms → `inductive Step` + adequacy
  theorems (PROJECT_PLAN §7); opportunistic: float shortest-roundtrip formatting,
  histogram-driven builtins, the sketch §5 export cross-check.
- Draft artifacts 07–10.
