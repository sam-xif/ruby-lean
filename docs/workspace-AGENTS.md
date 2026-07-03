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
- **Not started:** the Lean model itself; prong-2 fuzzing; prong-3 agent generation at
  scale; artifacts 07–10 (param binding, core library, metaprogramming, Rails slice).

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
- Prong 2: a Superion-style generator that drops `.rb` into `corpus/` (driver already
  consumes any corpus dir). Design/feasibility written up in
  [`harness/desugar-dt/prong2-design.md`](harness/desugar-dt/prong2-design.md) — not yet built.
- Begin the Lean model (artifacts 01–02 → `inductive Step` + fuel interpreter) once the
  desugar exit criterion (artifact 06 §7) is met.
- Draft artifacts 07–10.
