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

> ### ⚠️ CURRENT SNAPSHOT (2026-08-03) — read this first
>
> The detailed log below is **historical and partly superseded** (it is kept as the
> build record). Verified current state:
>
> - **Desugar: 1227/1299** bootstraptest agree, 0 disagree — effectively done; the
>   remaining 72 are the unsupportable/deferred set.
> - **Lean model: 940/1304** tier-0 agree, **0 disagree** (`--sut lean` GREEN; was
>   722 before the 2026-08-03 batch). Tier-1 (n=400, seed 7) 371 agree / 0 disagree;
>   tier-3 + regression replays clean. **`lean/README.md` §Fragment is the
>   authoritative list**; `lean/implementation-notes.md` L62–L73 is the build record.
> - **What the model now covers** beyond the L0–L2 core: a **prelude** (Ruby's core
>   library written *in RubyCore* — Enumerable/Comparable/`Range#each`/Hash overrides
>   — so a missing builtin costs a few lines of Ruby, not a new Lean rule); the
>   **reflective metaprogramming core** (`define_method`, `class_eval`/
>   `instance_eval`/`instance_exec`, `prepend`, `alias_method`, `singleton_class`,
>   ivar/const reflection, `Class.new`); **`defined?`**; **class variables**;
>   **`catch`/`throw`** + `redo` in blocks; **payload-core subclassing**
>   (`class MyString < String`); full **`zsuper`** param shapes; **visibility**
>   (`private`/`protected`/`public`, enforced at dispatch); `Kernel`/`Numeric` in the
>   ancestor chain (byte-exact `ancestors`); `Array#[]`/`String#[]` slices;
>   `dup`/`clone` copying ivars.
> - **Top remaining gates** (356 tier-0): string `eval` family (48, permanently out
>   of scope), `Rational`/`Complex` (43), blockless `Integer#times`/`Enumerator`
>   (22), `Regexp` (20), `Struct` (16), dynamic keyword keys (14),
>   `TracePoint`/`File`/`RubyVM` (22, out of scope). Re-measure with
>   `difftest run --tier 0 --sut lean` + `cases.jsonl` rather than trusting this.
> - **The next structural lever is dispatching repr, not more builtins.** `Struct`
>   and `Rational` are both blocked on the same thing: their `inspect`/`==` cannot
>   live in the prelude, because defining those names flips the *global* `reprPure`
>   flag and every `puts` in every program would gate. Making `p`/`puts`/
>   interpolation **dispatch** `to_s`/`inspect` retires that flag and unlocks ~59
>   cases plus every user class with a custom `to_s`.
> - **Metatheory: type safety as reachability, proved** — `invariant_sound` over the
>   full `stepFn`, and T5 `class_hierarchy` proved type-safe **Direction B,
>   axiom-clean** (`lean/RubyCore/Proof/`, impl-notes L51–L57); re-verified against
>   the new machine (L73), still axiom-clean.
> - **Checkers built:** Phase-1 random witness search (`lean/RubyCore/Search/`, L58)
>   and a **concolic engine** (`concolic/`, 28 tests) that solves for witnesses random
>   search cannot reach — with **the Lean model as its executor**.
> - **Two traps before touching `stepFn`** (L73): a `partial def` or a
>   `String.endsWith`/`startsWith` on the dispatch path is not kernel-reducible and
>   silently breaks every proof while the difftest ratchet stays green. Build the
>   `Proof/` files at batch boundaries.

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
  assignment-call `a[i]=v` value is the RHS; do-while `begin…end while` gated) → 752/1299.
  **L1 block front-end done (C21):** `yield` head, `block` extended to `[:block, params,
  locals, body]` (block-locals un-gated), `->` desugared to a `lambda` send → 792/1299.
  **L1b block passing done (C23–C24):** block-capture param `&blk` (carried as a `"&blk"`
  flat-string, mirroring `*rest` — no structured-param migration) + call-site block-pass
  `foo(&expr)` (new `[:blockpass, expr_or_nil]` head sharing the send/super block slot;
  covers `&:sym`/`to_proc`, `&nil`, anonymous `&`, forwarding, and the `&`-operand
  eval-order obligation via linearize) → **852/1299 bootstraptest agree, 0 disagree,
  0 harness-error** (`Export::VERSION` bumped 2→3; the **Lean model now consumes v3** — see
  below — so `--sut lean` is green again). `bin/coverage` tracks a ratchet (baseline 852). Deferred: single-RHS
  massign (to_ary), `const`/`@@x` `||=` (need `defined?`), indexed/attr **op**-assign,
  optional/keyword params + double-splat `**`/kwargs (M2), `...` forwarding, constant paths
  `A::B`, do-while, `super` arg-forwarding subtleties.
  **Desugar driven to full practical coverage: 1227/1299 bootstraptest agree, 0 disagree,
  0 harness-error, 0 AST-idempotence** (M2–M7, C25–C29; round-trip **1267 agree** incl. 40
  seeds, rule coverage 73/73). Landed across five ratcheted batches:
  - **M2 (C25):** `def`/`defs`/`block` param slot migrated flat `[String]` → structured
    param nodes (`:preq`/`:popt`/`:prest`/`:pkey`/`:pkwrest`/`:pblock`/`:pfwd`/`:pdestr`);
    keyword call args as a brace-less `[:kwargs,…]` marker (Ruby-3 separation). `852→1006`.
  - **M4 (C26):** `case`/`when` → if-chain over `===` (subject once; splat-when); `defined?`
    head. `1006→1048`.
  - **M5 (C27):** constant paths `A::B` — `[:cpath]`/`[:cpath_asgn]`, definition-position
    path names. `1048→1085`.
  - **M6 (C28):** `for`/`redo`/`undef`/`alias` heads, regex → `Regexp.new`, interpolated
    symbol, `...` forwarding, single-RHS massign (`to_ary`). `1085→1198`.
  - **M7 (C29):** indexed/attr op-assign, numbered params, do-while, nested + block-param
    destructuring, `$1`/`$&`, `rescue *classes`. `1198→1227`.
  `Export::VERSION` 3→4 (breaking param-slot + `kwargs`, then additive heads; `--sut lean`
  red until the Lean decoder migrates its param slot + adds the new heads). The remaining
  72 non-in-fragment programs are the unsupportable/deferred set: string `eval`-family (52),
  top-level `return` that bypasses the observation wrapper (6), un-parseable (5), plus
  documented gates (`__LINE__`/`__FILE__` reflection, backtick x-strings, flip-flop) and
  deferred `case/in` pattern matching + dynamic alias/undef names.
- **Lean model: L0 + L1 + L2 (object model) implemented and difftesting** ([`lean/`](lean/README.md), per the
  sketch [`docs/semantics/lean-model-sketch.md`](docs/semantics/lean-model-sketch.md)):
  small-step machine (kont stack + frame store), fuel interpreter, Ruby-faithful
  repr/error-message layer, oracle-generated CRuby name tables for dispatch fidelity
  (unmodeled builtins gate as `Unsupported` instead of mis-dispatching), and the SUT
  executable wired into the difftest engine as `--sut lean` (source → desugar →
  RubyCore JSON → Lean → Observation). **L1 blocks/procs/lambdas now in the executable
  stepper** (export v3; `lean/implementation-notes.md` L16): Proc as a heap object,
  frame-identity generative jump targets (`captured`/`home`/targeted `retJ`), `yield`/
  `block_given?`/`&blk`/block-pass/`&:sym`/`proc`/`lambda`/`->`/`Proc.new`/`Proc#call`,
  and proc-vs-lambda `next`/`break`/`return` with shared-scope locals. **Baseline: full
  bootstraptest 468/1304 agree, 0 disagree** (372 pre-L2; **L2a+b+c done** — `class`/`module`
  definitions, `Class#new`+`initialize`, cref-scoped constants, `method_missing`, frozen-`@x=`
  (`impl-notes L17`), `super`/`zsuper` (`L18`), singleton methods/eigenclasses
  `def self.m`/`class << o` (`L19`); rest gated Unsupported: upstream desugar
  (optional/kw params), iterating-builtins-that-yield, mixins/`@@cvar`/class-macros,
  unmodeled methods+constants); tier-1 fuzzing already
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
| `concolic-dataflow.md` | **design, implementation in progress:** emitting *dataflow* from the model as a **φ-free trace-SSA log** so the concolic engine needs no AST walk — the requirement (`derived.rb`: a condition is not a syntactic function of the inputs), why concrete traces can't recover it (value ambiguity), prior art (KLEE `ref<Expr>`/no-taint-flag, Rosette symbolic reflection, Serval, K's two-backend split), design space D0–D4, **why static SSA from the desugarer was rejected** (§5), the recommended observation-driven **symbolic shadow machine** (no `stepFn` changes) that **self-checks against the concrete run**, `$__inK` global as the input marker, staging S1–S4, and symbolic *dispatch* via guarded splits as the payoff |
| `search-and-proof.md` | **brainstorm (2026-08-03):** where this checker sits on the concrete↔symbolic spectrum, and **how Directions A and B compose**. Rosette's symbolic reflection adapted as *finite-domain exhaustive case-splitting via directed goals* (D5) — concrete boot makes the interesting domains finite, so it may retire theory-of-arrays for the nil-bug class; *measured*: input-bounded loops put the symbolism in the **path condition** (trip count), so the result is constant per path and collection opacity cost nothing; branch distance / gradient guidance (Korel, Angora, NEUZZ) and why summary inference beats it; loop summaries from samples vs from the code; CHC/Spacer as the concrete "untrusted engine" that discovers invariants for `invariant_sound` to check. Full literature table with verified-vs-recalled markers |
| `PROCEDURE-authoring-semantics.md` | **agent playbook** for authoring/extending these artifacts against a Ruby oracle |
| `linearization.md` | worked example of nontrivial desugaring: hoisting control-flow jumps out of operand position (`"#{next}"`) |
| `co-semantics.md` | **framing (early draft, to grow):** Ruby + Rails as a *pair* of semantics at two altitudes joined by a refinement/bisimulation correspondence — structural `α` where macros define methods, observational `α` where `method_missing` does not; correspondences testable via `obs⁺` before the Lean model exists. §5: proof-goal shape (coupling invariant `Inv`, stuttering forward simulation — same machinery as `relating-language-and-substrate.md` — `escape` event for invariant-breaking programs, miniRails not real Rails in the proof). §6: everything hinges on `Inv` — clause taxonomy + validate it as an executable heap predicate against CRuby first |
| `types-and-preservation.md` | **research artifact (to grow):** (A) formalization-oriented deep dive on **Sorbet** (type grammar, flow-sensitive narrowing, unsound-by-design stance + escape hatches, `# typed:` strictness levels, runtime `sig` enforcement as the gradual boundary via `T.untyped`); (B) broad survey of how **type preservation/soundness** is proved (Wright–Felleisen, Featherweight Java + "stupid casts", TypeScript/Safe-TypeScript + store typing `Σ`, DRuby/PRuby, Typed Racket occurrence typing, gradual-typing safety + blame theorem + gradual guarantee, Lean/Coq/Isabelle mechanization); (C) maps onto our `Step` — recommends a *runtime* three-outcome safety statement, reuses `Step.heap_monotone` as store typing, treats a sig-violating heap mutation as a type `escape` (cf. `co-semantics.md` §5.3); two cheapest steps (`obs⁺` gradual-guarantee probe, `srb`/`T.reveal_type` typing oracle) need no Lean. Verified via adversarial research pass; two refuted claims recorded as corrections (`T.cast` *is* runtime-checked; `T.let` isn't the only dual-checked assertion). §C.5: the discipline decision (extrinsic typing + store typing `Σ` over the machine) + Lean shape |
| `certificate-language.md` | **design + §9 as built (C0–C4 done, 2026-08-25):** type-checking as **certificate replay** — the untrusted-emitter/trusted-validator pivot (back to `../type-safety-by-reachability.md` §4/§6). The `Cert` grammar (`theta`/`deltaRows`+provenance/`bodies`/`ledger`/`assumes`) reusing `Assn`/`Row`/`ASig` as the vocabulary; `validate` search-free; **`validate_sound` proved** as the composed program-level theorem through `invariant_sound`; design dimensions D1–D6; milestones **C0–C9** with gates, measured against the slice census + the **fourth ratchet** (bodies certified-by-replayed-certificate, now **11**). §9 records the corrections the build forced: what a certificate *is* is the **declaration table** (so §3's bridging lemma is unnecessary — `nominalOk` *is* `CtlOk`'s clause); `.fromDef` is unsound at `Machine.init p` and belongs to C9's heap phases; the kernel-replay cost is inherited from `infer`'s WF recursion, not created; and the two rungs the measurements name as **coming before C5** — R2 (name-global `declaresName`, now blocking three separate things) and an `Assn` atom for a **constant** (61% of the 85-`needed` census is class-object receivers, i.e. constant reads). Implementation: `lean/RubyCore/Cert/` + `Proof/Cert/` (trusted, **V1–V8**), `certify/` (untrusted, **E1–E16**) |
| `judgment-layer.md` | **design + built through J35 (2026-08-27): the re-scoping of C-1** — state the invariant over an **inductive judgment** (`Judge`/`KJudge`/`MachineTyped`, transcribing `type-judgments.md` §6–§8 into Lean as the definition of record) instead of over `chk`. **Built:** machine typing + preservation over `Judge` (J20–J27), the derivation-certificate pipeline (J2/J28), and the **semantic judgment** `SemJudge` (J29/J30, `Proof/Judgment/Sem.lean`) — reachability-defined, `Judge`-free, with `judge_semJudge` as the fundamental lemma (adequacy of the syntactic system), `semJudge_sound` (type safety from a `SemJudge` however obtained — the extension point for out-of-fragment/Rails constructs), and `judge_result_vty` (terminating values inhabit the judged type, via the J29 answer-typed invariant); plus **semantic axioms (J31)**: user-specified semantic judgments as `Judge` leaves invoked from the `Deriv` certificate language (`Judge.semantic`/`Deriv.semantic`/`JCert.semAssumes`, `validateJ_certifies` conditional on one `EvalOkAt` obligation per claim), pilot end to end — `lambda { 1 }`, out of the syntactic fragment, obligation discharged by executing the semantics, certified from a data certificate (`Proof/Judgment/SemAxiom.lean`); and the **Rails pilot (J32–J35)**: claim *records* (claimed type + claimed **rows** + class-body gate), `define_method` made typing-visible (capture erasure for closed bodies + one-step composition, ratchet-verified), the invariant taught what a class body is (`inClassBody`, `self` = the definee; `NoHook` over `define_method`), and the goal program `class String; define_method(:shout) { 1 }; end; "a".shout` **type-checked at `.int`** — the obligation `semAxiomsOk_dm` discharged by executing the semantics, composed through both the hand derivation and a data certificate (`Proof/Judgment/Rails.lean`). Diagnosis: metatheory stated over a *function* is re-incurred at every checker rewrite (`infer.induct` → `chk.induct` → …); the relation is the churn-stable layer. Settles the **semantic type notion**: recursive knots tied by names into a table `D` (anonymous structural recursion is coinductive — refused); slots as heap-conformance invariants; responds-to sets indexed by boot phase; **unions + nil + narrowing** as the load-bearing grammar. Certificates become **derivations-as-data** checked by a constructor-mirroring local checker (`Deriv.check → Judge` is one easy induction); `chk` demoted to the coverage tier, `chk_table_ret` deliberately abandoned. Milestones **J0–J4** (`lean/RubyCore/Judgment/` + `Proof/Judgment/`, **J-numbers**); honest cost: preservation's content is unchanged, only its marginal cost structure improves. **The H-layer (J36, 2026-08-27, `lean/RubyCore/HJudge/`, `lake build HJudge`)**: iris-lean in the dependency graph (toolchain 4.32.2; sibling `mdd/ruby-sorbet`'s seat ported in-tree — `Language` instance over `stepFn`, `ownP` `stateIs`, WP walk tactics, `run_adequate_of_wp`), the semantic denotation `HTy` (the sibling's `STy` + `union` + the higher-order `sem` door; `HSub` = denotation inclusion; heap-generic intro lemmas via `self_mem_ancestors`), and **`HJudge` proved soundly type-safe on the SemJudge formula**: `HSemJudge` (= `SemJudge` with `VTy` → `τh.den`), the `vty_hden` bridge, four admission routes (`ofJudge`/`sem`/`wp`/`sub`), fundamental lemma `hJudge_semJudge`, `hJudge_sound`/`hJudge_result_den`, `run_lift_of_reaches` re-landing WP adequacy on `ReachableResult` — axiom-clean; worked ends past `Ty`'s reach (`true : TrueClass` in every environment; `(1).zero? : FalseClass` by concrete `rb_walk`; J35's `define_method` result as `is_a?` at the mutated final heap; `HTy.duck` decided at boot) |
| `typing-the-slice-milestones.md` | **plan (2026-08-30):** the machinery path from the measured baseline — *all six whole-file certificates carry zero rows*, `sem_assumes` = each file's `def self.x` count, so the accepts never look inside a body — to typed bodies. **M0** is the reordering finding: the slot frame (`slot-frame.md`) half-breaks this layer's own semantic-judgment discipline, because `SlotClaim.Holds` is a *single-state* predicate and `frameOkB` conflates it with a claim about the program text, so the property SF-T3 should prove is defined nowhere; fix is `SemFrame` (reachability-shaped like `SemJudge`, over intermediate states — a row is consumed at every dispatch) with `frameOkB` demoted to one of four admission routes. **M0a** is the cheap one found by censusing all eight files: the only AST head in the slice with no rung in any plan is `fwd` (argument forwarding), and it exists only because `class_sugar_strip.rb` expands `alias` into `def m(...) = n(...)` — no slice source contains `(...)`; the rule that falls out is *a strip transform may only emit heads that already have a rung, else gate*. Then **M1** metaclass hygiene (a module's eigenclass superclasses `Class`, not `Module`; `enterScopedClassBody` skips eager realization), **M2** qualified names pinning ids, **M3** `srows` (`slice-verdict.md` §4a rung 3 — designed, unbuilt), **M4** `self` at `.clsOf` inside a `defs` body (the J11 widening), **M5** the eigenclass-aware install walk (all 26 `opaque_` sites in the certificated files are `def self.x`), **M6** dropping name-globality (re-key + SF-T3), **M7** the bodies. Critical path M1→M2→M3→M4; ordering constraints M2-before-M5 (else a resolver can pick the wrong id — unsound) and M0-before-M6 (else a proof is replaced by a check). Interlocks with `homebrew/slice-inventory.md`, which prices the *judgments* this sequences the machinery for |
| `type-judgments.md` | **spec (implementation catalog, to grow):** the typing layer's reference — every judgment form (`Ty`, `Sub` [= the `ancestors` walk], `Consistent`/`≲` [gradual boundary, non-transitive], `Join`, `mtype` [= store-typing mirror of `Heap.lookup`], `narrow` [occurrence typing], `HasType` [engine, one rule per `Expr` head, `send` is the whole game], `KontOk`/`ConfigTy` [type the machine state, not just exprs], `StoreOk` [`Δ ⊨ H`]); metatheorem statements (preservation up-to-subtyping / progress / gradual three-outcome safety); staging T1 (the exact fragment already in `Proof/Step.lean`) → T2 send → T3 gradual → T4 flow-sensitivity → T5+ generics. Companion to `types-and-preservation.md` (rationale). Extrinsic discipline: defined over the untyped syntax, reuses `Step.heap_monotone` as store growth |

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
`corpus/tier3/`), **tier 4** (the **Sorbet** corpus — see below), and **mixed campaigns**
(`run --mix tier1=0.9,tier0=0.05,tier3=0.05`,
Hypothesis-hosted so shrinking survives). Tier 2 (mutating scraped Ruby) is a stub slot,
deliberately deferred until the corpora exist to seed it. Built-in SUTs: `stub`,
`identity` (smoke test), `desugar` (adapter over `harness/desugar-dt/`; `--inject-bug` is
the detection self-test), `lean`, and `sig-strip` (the gradual-guarantee probe).

**The Sorbet corpus runs in the Lean model (2026-08-05).** `run --tier 4 --sut lean` is
**14/18 agree, 0 disagree, 4 unsupported** (was 1 agree / 17 disagree). Two changes got it
there: **`Module#method_added` now fires on `def`** (`lean/implementation-notes.md` L79 —
a pre-existing fidelity gap, and the hook sorbet-runtime's `sig` is built on), and a **`T`
prelude shim** (L80) carrying Sorbet's runtime half as ordinary RubyCore — the assertion
family, the type constructors, and real **sig enforcement** via `alias_method` +
`define_method`, which is §C.2's "a sig is heap mutation replacing a method-table entry
with a checking wrapper" made literal. Consequence for the soundness work: a
sig-boundary `TypeError` is now an ordinary reachable outcome of `stepFn`, so `typeStuck`
and `invariant_sound` apply to it with no new machinery. Still gated: `T::Struct`,
`T::Enum` (structural, not annotations — they gate honestly rather than NameError).

**Sorbet safety is stated and proved, both directions (2026-08-06).**
`lean/RubyCore/Proof/SorbetSafety.lean` (L81) makes §C.1's three-outcome runtime statement
a formal object by **reusing `TypeSafety.lean` with the bad state weakened** —
`sorbetStuck := typeStuck ∧ ¬ isBlame`, blame being sorbet-runtime firing at a boundary,
i.e. the type system working. Axiom-clean: `sorbet_invariant_sound` (Direction B) plus the
Direction-A certificates including `run_blame_sorbet_safe`; `sorbetStuck_typeStuck` proves
the weakening only removes outcomes, so existing certificates transfer.
`SorbetConcrete.lean` certifies real corpus programs through the **prelude-booted** model
(the property is stated over that machine — over `Machine.init` there is no `T` at all and
the theorem would be about nothing): `sig-basic/000` safe by value, **`sig-basic/001` safe
by *blaming*** (the whole content of the weakening), `untyped-boundary/000` refuted.
`lean/RubyCore/Types/Fragment.lean` (L82, `rubycore --fragment`) pins the *scope*
executably — 6/18 of the corpus in-fragment, 3 in scope once intersected with srb
acceptance, and **no unsoundness witness is in the fragment** (guarded). Not claimed:
"srb accepts P ⇒ P is Sorbet-safe" — that needs Sorbet's static judgment (`type-judgments.md`
T1–T3), which is the next build.

**Sorbet scaffolding (tier 4, 2026-08-05)** — the no-Lean-needed half of the
Sorbet-soundness plan in [`docs/semantics/types-and-preservation.md`](docs/semantics/types-and-preservation.md)
§C.3 is built and runnable: `corpus/sorbet/` (18 programs taxonomized by Sorbet design
feature, each with a sidecar declaring the expected outcome of *both* halves);
`difftest sorbet check` (the `srb tc`-vs-actual-behavior two-by-two — **4 unsoundness
witnesses, 2 conservative rejections, 0 declaration mismatches**); and
`run --tier 4 --sut sig-strip` (the **gradual-guarantee** probe over a Prism sig-stripping
transform — **10 agree, 5 licensed weakenings, 3 gated, 0 violations**). Two findings
worth knowing before building on it: sorbet-runtime's checking wrapper is visible through
reflection (a genuine guarantee violation, kept as the probe's detection self-test, N33),
and the Lean SUT false-disagrees on all of tier 4 because the model's `require` returns
true for a library it does not have (N34 — fix specified in
`../type-safety-by-reachability.md` §10.4; do not mix the `sorbet` arm with `--sut lean`
until then). See [`difftest/README.md`](difftest/README.md) to run it,
[`difftest/HANDOFF.md`](difftest/HANDOFF.md) for the fresh-context hand-off (state,
load-bearing invariants, enhancement queue), and
[`difftest/implementation-notes.md`](difftest/implementation-notes.md) for non-critical
implementation choices (N1–N34, committed for rollback).

### `lean/` — the Lean 4 model (runnable SUT)
The mechanization of artifacts 00–04 begun from the sketch. See
[`lean/README.md`](lean/README.md) for layout, build (`lake build`, toolchain pinned),
the L0 fragment inventory, and the two fidelity policies (three-way lookup-miss split;
`reprPure` gating); [`lean/HANDOFF.md`](lean/HANDOFF.md) for the fresh-context hand-off
(state, coverage assessment — 372/1304 bootstraptest
cases, 0 disagree — and the ordered next steps: L1 blocks done, next L2 classes then
`inductive Step`); [`lean/implementation-notes.md`](lean/implementation-notes.md) for
revertable decisions (L1–L16). `RubyCore/CRubyNames.lean` is **generated** by
`lean/scripts/gen_cruby_names.rb` against the pinned oracle. The harness↔Lean interface
is `harness/desugar-dt/lib/export.rb` (versioned RubyCore JSON; `bin/export-json`).

`RubyCore/Cert/` + `RubyCore/Proof/Cert/` are the **certificate language**
(`docs/semantics/certificate-language.md`), deliberately isolated: import-only against
`Types/`/`Proof/Static/`, with `Main.lean`'s `--certify` the single wiring point.
`Format.lean`/`Validate.lean`/`Ledger.lean` are the trusted checker (the JSON codec is
split out into `Json.lean` because `Lean.Json.parse` does not reduce in the kernel);
`Proof/Cert/Sound.lean` proves **`validate_sound`** — *this certificate, this program,
therefore no reachable `typeStuck`, conditional only on the printed residue* — and
`Proof/Cert/Ledger.lean` closes `discharge_sound`'s premise that L262 left open.
Decisions: [`lean/RubyCore/Cert/implementation-notes.md`](lean/RubyCore/Cert/implementation-notes.md)
(**V1–V8**).

### `certify/` — the untrusted certificate emitters (runnable)
The **generation** half of `docs/semantics/certificate-language.md`, and everything in
it is on the untrusted side of that document's §1 trust boundary: a bad certificate
costs a body we failed to certify, never a false "type-checked". Talks to Lean *only*
through the versioned certificate JSON (`rubycore --certify FILE`) — nothing here links
against or patches the Lean tree. `certify.py` is one CLI: `emit` (self-certification
from `--assn`), `validate`, `ledger` (C2's coherent single-class pairing), `solve`
(C3's `theta`), and `ratchet` — the **fourth ratchet** over the slice, plus the
`needed`-census classification that is C3's own measurement. `rbi.py` ingests Sorbet
`sig`s (C4), `core-rows.txt` is the hand-written core-library stand-in (the checkout
ships no core RBI), `tyjson.py` the wire encoding, and `llm.py` is C4's **LLM arm**
(`--llm`): Claude is given the file, every per-body verdict, the type language
positively *and* negatively, and the one-row-per-name rule, and returns rows under a
JSON schema. Responses are cached under `certify/certs/llm/` and **committed** — a
ratchet whose number depends on a live sample is not a ratchet — with `--llm-offline`
for cache-only runs and `--llm-refresh` to re-ask deliberately. Calls stream with a
progress heartbeat and a timeout set from the measured latency distribution, both of
which exist because E18a's first draft misdiagnosed a slow call as a hung one. See
[`certify/implementation-notes.md`](certify/implementation-notes.md) for revertable
decisions (**E1–E18**) — including the measured ones: the settling pass that caught a
wrong `Token#to_s : Float`, the greedy plateau that needed a second starting point
(6 → 10 on `version.rb`), why all six remaining ratchet bodies are blocked by R2, and
E18's result — the LLM proposes 69 rule-respecting rows and the ratchet does **not**
move, because generation is not the bottleneck: three *schema* limits are (R2, no
`Assn` atom for a constant, no inherited-declaration lookup).

### `concolic/` — finding type errors by concolic execution (runnable)
Phase 2 of the Direction-A witness finder: a **concolic search engine** (Python + z3)
that *solves for* inputs driving a program to a **type-stuck** outcome. Finds
`n == 123456789` behind a narrow guard in 2 iterations — the case Phase 1's random
search (`lean/RubyCore/Search/Random.lean`) provably misses even at a 20x budget.
**The Lean semantics is the executor**: the `rubycore-concolic` exe
(`lean/ConcolicMain.lean`) runs the real `stepFn` and supplies both the branch
decisions and the authoritative outcome, so the engine holds no method tables and
no error classification of its own and cannot drift from the model (branch
decisions are observable at the configuration level, so `stepFn` is untouched).
The search loop is still **untrusted** — it only proposes inputs; witnesses are
confirmed against CRuby and the plain `rubycore` observation path. See [`concolic/README.md`](concolic/README.md) to
run it and [`concolic/implementation-notes.md`](concolic/implementation-notes.md)
for revertable decisions (K1–K8).

### `ratchet/` — a certificate-checking ladder, restarted small (runnable, isolated)
A **restart** of the type-checking work (2026-08-31), deliberately isolated from `lean/`,
`certify/`, and the judgment layer (own `lakefile.toml`/`lean-toolchain`, no import of
`RubyCore`). **`Expr`/`Ty` are ported verbatim** from the real model
(`lean/RubyCore/Syntax.lean`/`Types/Ty.lean`) rather than invented, and every corpus program
is **real Ruby run through the real desugarer** (`harness/desugar-dt/bin/export-json`), not a
hand-authored AST — the certificate is a flat list of claims keyed on real `Expr` subterms by
structural `==` (exactly why `Expr` derives `BEq` in the real model), not a parallel
type-annotated shadow tree. Same `validate : Cert -> Expr -> Bool` shape as `certify/`'s
`Cert`/`Validate.lean`. **89-rung corpus**, 8 tiers: literals → arithmetic/string/bool `send`s
(a small hardcoded builtin table plus a claims-based escape hatch, incl. indexing, which is
just `#[]`) → `var`/`vasgn`/`seq` (real mutable-local scoping) → conditionals/`elsif` →
arrays/hashes → top-level functions (declared via a claim on their own `def` node, incl. a
self-recursive one) → **classes** and **modules** (26 rungs, real construction/ivars/
inheritance/`super`/singleton-methods, all deliberately `expect_validate: false` — `chk` has
no rule for `class'`/`module'`/`defs`/`super'` yet, tracked honestly rather than faked).
Deliberately not yet ported: the semantics (no `stepFn`/interpreter, so no dynamic execution
check) — see `ratchet/AGENTS.md` §Frontier for what's next (environment merging across `if`
branches, non-required params, blocks, then classes/modules, then finally the semantics).
Every commit that extends `chk` for one more construct is meant to move a tier's fraction
visibly, instead of growing by tackling another whole slice at once.
See [`ratchet/AGENTS.md`](ratchet/AGENTS.md); run with `ratchet/scripts/run_ratchet.sh`.

### `playground/` — visual step-through of the Lean stepper (runnable)
A browser playground to write Ruby and step through its execution **in the Lean
model** one `stepFn` transition at a time (control state, frame stack + live
locals, continuation stack, stdout). Zero-dependency Python stdlib server
(`server.py`) over the existing pipeline + a Lean `--trace` mode
(`lean/RubyCore/Trace.lean`, a lossy non-gating tooling view). It also runs the
**static** queries on the same source without executing it: **Type-check
(infer)** is `rubycore --check` (the nominal whole-program `infer`, with
`--fragment`'s violations beside it, since `uncertified` is usually explained by
them) and **Per-body (inferOpen)** is `rubycore --assn` — the assertion-language
report of `homebrew/assertion-language.md` §11, one verdict per method body, in
the three-line shape `Assn.explain` prints. Run: `cd lean && lake build`, then
`python3 playground/server.py`. See
[`playground/README.md`](playground/README.md).

### `spikes/` — quick experiments and proofs of concept (runnable)
Throwaway-by-default measurements: a memo fixes a threshold, a spike measures it,
the number lands in the owning doc's session log. **Nothing here is on a build
target and nothing under `lean/RubyCore/` imports it** — Lean spikes are run with
`cd lean && lake env lean ../spikes/<dir>/<File>.lean`, and a spike that needs a
library definition weakened copies it under a different name rather than editing
it, so no theorem can come to depend on the weakening. See
[`spikes/README.md`](spikes/README.md).
Current: [`spikes/slot-frame/`](spikes/slot-frame/RESULTS.md) — E2/E3 of
`docs/semantics/slot-frame-experiment.md` (both pass; E4 answered as a byproduct
and it fails on `def self.x`).

### `homebrew/` — coverage analysis + the **active initiative** (runnable)
**Start at [`homebrew/PLAN.md`](homebrew/PLAN.md)**, then
[`homebrew/HANDOFF.md`](homebrew/HANDOFF.md) (state of play, what is in flight, next steps)
and [`homebrew/slice-gates.md`](homebrew/slice-gates.md) (the live coverage tracker —
`difftest gates`). **Status 2026-08-13: M1–M8 done.** Criterion 1 is close but not closed —
all four corpora at **0 disagreements** (tier-0 **991**, slice **349/355 running, 3 gated**,
domain **10,000 inputs**, tier-4 **25**), with the last 3 gates being byte strings, whose
representation half is landed and whose prelude half is specified in the handoff. Criterion 2
(the type checker, M9–M11) is not started. — the build plan for taking Homebrew's
CVE-matching decision core (`version.rb` + `vulns/{semver,cvss,purl,vulnerability,identify}.rb`,
~1,876 lines, ~360 spec examples, zero effects) end to end: desugar → model → difftest →
type check → soundness. Nine workstreams (front end, regex engine, linker, difftest,
checker T2–T7, proof, demonic mocks, LLM type-fill, the finding), 12 gated milestones,
five fixed decisions, and the working norms (`implementation-choices.md` per decision,
one commit per entry, no file over 1,000 lines).

Measurement of Homebrew (`Library/Homebrew`, 962 files / 147k lines / 7,777 sigs,
`# typed: strict` throughout) against all three layers. Headline (2026-08-10): desugar
**589/962 files**, three small syntax features from ~97%; the executable semantics
already resolves **93.6% of the 113,610 call sites**, with the 6.4% gap concentrated in
`Pathname`/`File` (§2.2 — scope an **FS-lite `F` component of our own** rather than
waiting on `../posix/`; network reduces to a subprocess oracle), `Regexp`, and a
prelude-sized Enumerable tail; whole-program execution is ruled out on six independent
grounds (§2.1) with `rubocops/` as the one genuinely executable subtree; the
**Sorbet fragment admits 6.4% of methods** (erased generics + `prepend` + `T.untyped` are
the blockers) and the checker answers `unknown` on every file, because its type language
is `Int|Bool|Nil|Sym` and Homebrew's types live in **280 RBI files**. `scan.rb`
(desugar-fragment scan + RubyCore export), `census.rb` (unbiased Prism census),
`analyze.py` (report), `closure.py` (rank candidate slices by require-closure purity).
See [`homebrew/README.md`](homebrew/README.md), plus
[`homebrew/execution-by-mocking.md`](homebrew/execution-by-mocking.md) (linker + typed
mocks: feasible; RBIs first, LLM last; demonic mocks are sound for Direction B; the
load-time-heap objection is 111 files once sorbet-runtime is excluded) and
[`homebrew/first-complete-slice.md`](homebrew/first-complete-slice.md) (**full
enumeration of candidate slices** + the race target: **the version + vulnerability
stack** — `version.rb` under `vulns/{semver,cvss,purl,vulnerability}.rb`, ~1,530 lines,
zero effects, ~270 existing spec examples, no RBI ingestion needed. Structural finding:
the require graph has **one 227-file cycle**, so every formula-touching subsystem —
including `cli/parser` — has a 501-file / 80k-line closure and the core cannot be sliced.
Headline the slice supports: Homebrew carries **two inequivalent version orderings**
(`::Version#<=>` and `Vulns::Semver.compare`) and uses both inside the same CVE-matching
decision).

**Reportable findings live in [`homebrew/repro/`](homebrew/repro/README.md)** — nine
Direction-A witnesses reproducing from the **unmodified `brew vulns` / `brew
advisory-match` commands** against a pinned upstream checkout, with the OSV network
stood in for at the process boundary (`HOMEBREW_CURL_PATH` → a stand-in `curl`, so no
Homebrew source is patched and `JSON.parse`/`sig`/`T.let` all still run). `run.sh --all`
is the self-check; [`repro/WITNESSES.md`](homebrew/repro/WITNESSES.md) is the triage note,
ranked by realism, and discharges `nontrivial-target.md` R2. The vendored checkout is
gitignored — recreate it with `repro/fetch-brew.sh`, then `repro/setup.sh`.

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
- **When extending the Lean model (`lean/`):** work the same way as the desugar.
  - **Ratchet discipline (load-bearing):** after every change re-run `--sut lean` on tier-0
    (`cd difftest && uv run python -m difftest run --tier 0 --sut lean`), plus tier-1 fuzzing
    + regression replay at batch boundaries. **0 disagreements at every commit**, agreement
    only ever goes up; a new feature that would disagree must instead **gate `Unsupported`**
    (exit 3) — a partial model declares what it doesn't cover rather than guessing. `MODEL-BUG`
    (exit 1) is never acceptable in a commit. Verify new behavior against the CRuby oracle
    (`harness/desugar-dt/bin/export-json <file> | lean/.lake/build/bin/rubycore`) with minimal
    discriminating snippets before trusting it (`[V]`).
  - **Commit in small, logical increments** — one head / one coherent feature per commit,
    each with its own ratchet number in the message (`NNN->MMM, 0 disagree`), so any
    regression is bisectable. Do **not** batch unrelated features into one monolithic commit.
- **Decisions:** record non-critical harness choices in `implementation-choices.md` (desugar)
  or `implementation-notes.md` (Lean model, difftest engine), **committed** so any decision
  is revertable. Note *every* non-trivial implementation decision, not just surprising ones.

## Environment

- Oracle: **CRuby 4.0.5** installed via Homebrew (`$(brew --prefix ruby)/bin/ruby`, has
  `+PRISM`). System Ruby 2.6 is too old. RVM failed to compile (deprecated `openssl@1.1`).
- Run the harness: `RUBY=$(brew --prefix ruby)/bin/ruby; $RUBY sam-xif/ruby/harness/desugar-dt/bin/run`.
- `bootstraptest/` corpus is harvested on demand (not vendored); recipe in the harvester header.

## Git

- Work happens on branch **`sam-xif-investigation`** (based on `origin/main`).
- Commit messages end with the project's `Co-Authored-By` trailer. Commit/push when asked.

## Open threads / next steps

- **Desugar fragment driven to full practical coverage: 1227/1299 bootstraptest agree, 0
  disagree, 0 harness-error** (M1 → M7, implementation-choices C12–C29; round-trip 1267
  agree incl. seeds, rule coverage 73/73). M2 (structured params + kwargs), M4
  (`case`/`defined?`), M5 (constant paths), M6 (`for`/`redo`/`undef`/`alias`/regex/`...`/
  single-RHS massign), M7 (op-assign/destructuring/do-while/`$1`) all landed with per-batch
  ratchets. The remaining 72 are the unsupportable/deferred set (string `eval`-family 52,
  top-level `return` 6, un-parseable 5, + documented gates for `__LINE__`/`__FILE__`,
  backtick x-strings, flip-flop, and deferred `case/in` pattern matching + dynamic
  alias/undef names). Remaining desugar work is small and mostly out-of-scope; the next
  lever is the **Lean model** consuming export v4 (below).
- Prong 2/3 are now realized as the standing **`difftest/` engine** (Python; tier 1 =
  Hypothesis scope-aware fuzzing per [`harness/desugar-dt/prong2-design.md`](harness/desugar-dt/prong2-design.md),
  tier 3 = AI-generated adversarial corpus). Grow it: more tier-1 vocabulary (classes,
  splats, kwargs), tier-3 corpus across all categories, tiers 0/2, and eventually the Lean
  interpreter as a SUT. Verified end-to-end: identity SUT 200/200 agree; desugar SUT with
  `DESUGAR_BUG=1` yields a shrunk minimal disagreement.
- **Lean model (begun; `lean/`):** grow the L0 fragment along the difftest
  `Unsupported`-reason histogram (same ratchet discipline as the desugar: 0 disagree,
  agreement only goes up; baseline 372, was 295 pre-L1). Ordered plan in
  [`lean/HANDOFF.md`](lean/HANDOFF.md): desugar M2 (biggest lever, 544 cases gate
  upstream) → L1 blocks/`yield` (done) → L2 class forms → `inductive Step` + adequacy
  theorems (PROJECT_PLAN §7); opportunistic: float shortest-roundtrip formatting,
  histogram-driven builtins, the sketch §5 export cross-check.
- Draft artifacts 07–10.
