# RubyCore Quasi-Formal Semantics

Design artifacts for the Lean model described in `../../PROJECT_PLAN.md`. These document
the semantics we intend to mechanize — precise enough to translate to Lean rules, but
not yet Lean code.

## Reading order

| # | Artifact | Covers |
|---|----------|--------|
| 00 | [Notation & abstract syntax](00-notation-and-syntax.md) | machine config `⟨K,H,Ξ⟩`, frames, judgments, RubyCore grammar, desugarings, observation function |
| 01 | [Object model, values & heap](01-object-model.md) | value domain, objects/classes as heap data, eigenclasses, identity, truthiness, freeze |
| 02 | [Dispatch & MRO](02-dispatch-and-mro.md) | ancestor-chain construction, lookup, send, `method_missing`, `super`, visibility |
| 03 | [Variables, scope & constants](03-variables-scope-constants.md) | 5 namespaces, local/block scoping, class vars, two-phase constant lookup |
| 04 | [Blocks, procs & control flow](04-blocks-procs-control-flow.md) | closures, proc-vs-lambda, `yield`, `return`/`break`/`next`/`redo`/`retry`, exceptions/`ensure` |
| 05 | [Differential-testing methodology](05-differential-testing.md) | oracle harness, `obs` normalization, test sources, generation, metamorphic testing, disagreement triage, rule-coverage metric |
| 06 | [`desugar` and testing it first](06-desugaring-and-its-testing.md) | round-trip oracle (no RubyCore semantics needed), evaluation-order trace, three-pronged corpus (bootstraptest + fuzzing + AI agent), desugaring-rule coverage, exit criterion |

**Mechanization:** [Lean model sketch](lean-model-sketch.md) — the bridge from artifacts
00–06 to Lean 4, written from a close read of the two anchor papers: what we adopt from
Essence-of-Ruby (generative jump targets → `FrameId`s; the variable store → a frame
store unifying shared mutable locals *and* jump generativity; oracle-composition as a
module boundary) and from RIL (pipeline split, eval-order obligations as step-relation
seeds), what we reject (big-step, meta-level exceptions, maximal linearization), the
`Config`/`Step`/fuel-interpreter skeleton, and the L0–L3 fragment ladder that plugs into
the difftest engine as a SUT from day one. **Implementation begun:** the machine, fuel
interpreter, and SUT executable live in [`../../lean/`](../../lean/README.md) (L0
fragment, running as `--sut lean` in the difftest engine); the `inductive Step` relation
is still to be authored against it.

**Process:** [Procedure for authoring artifacts](PROCEDURE-authoring-semantics.md) — the
repeatable agent playbook for producing/extending these docs against a Ruby oracle.

**Technique:** [Linearization](linearization.md) — a worked example of why `desugar` is
nontrivial: hoisting control-flow jumps out of operand position (e.g. `"#{next}"`).

**Strategy / brainstorm:** [Search and proof](search-and-proof.md) — where the checker sits
on the concrete↔symbolic spectrum and **how Direction A and Direction B come together**
(*"search enumerates trip counts; invariants summarise them"*). Rosette's symbolic
reflection adapted as finite-domain exhaustive case-splitting via **directed goals**
rather than machine forking; the *measured* finding that input-bounded loops relocate the
symbolism into the path condition (so collection opacity cost nothing on the fold
benchmark); branch distance and why *summary inference* is the stronger half; recovering
summaries from samples (finite differences) or from the code (one symbolic loop
iteration); and CHC/Spacer as the concrete instantiation of the untrusted invariant
engine that `invariant_sound` was built to check. Includes a literature table marking
which references were verified in-session.

**Instrumentation design:** [Concolic dataflow tracing](concolic-dataflow.md) — how the
model should emit *symbolic terms* (not just branch directions) so the concolic engine can
build solver queries without re-deriving dataflow outside the semantics. States the
requirement (a condition is generally not a syntactic function of the inputs — see the
`derived.rb` counterexample), rules out reconstruction from concrete traces (value
ambiguity), and recommends a **symbolic shadow machine driven by configuration
observation** (no `stepFn` changes, mirroring the same `(ctl, kont-head)` discrimination),
with the key property that the shadow **self-checks against the concrete run** so
mirroring bugs degrade to lost precision rather than wrong constraints. Staged S1–S4;
§8.5 notes that symbolic *dispatch* — solving directly for inputs that force a dispatch
miss — is the payoff this layer enables.

**Framing:** [Co-semantics of Ruby and Rails](co-semantics.md) — an early design artifact
(to grow over time): Rails as a *second* semantics at a higher altitude, joined to the
core by a refinement/bisimulation correspondence (structural where macros define methods,
observational where `method_missing` does not). Reuses `obs⁺` and the metamorphic C2 lever
so correspondences are testable under CRuby *before* the Lean model exists. §5 gives the
precise proof-goal shape (coupling invariant `Inv` + stuttering forward simulation +
`escape` event + `obs_agree`; real Rails never enters the proof — miniRails does); §6
argues everything hinges on constructing `Inv` and lays out its clause taxonomy plus the
executable-`Inv` validation path (assert it on live CRuby heaps first).

**Types:** [Sorbet's type system & a preservation roadmap](types-and-preservation.md) — a
research artifact (to grow): Part A is a formalization-oriented deep dive on **Sorbet**
(type grammar, flow-sensitive narrowing, the unsound-by-design stance + escape hatches,
strictness levels, and runtime `sig` enforcement as the gradual boundary); Part B is a
broad survey of how **type preservation / soundness** is proved (Wright–Felleisen syntactic
method, Featherweight Java, the TypeScript formalizations + store typing, DRuby/PRuby,
Typed Racket occurrence typing, gradual-typing soundness + the blame theorem + the gradual
guarantee, and mechanization techniques); Part C maps both onto our `Step` relation —
recommending a *runtime* three-outcome safety statement, reusing the already-proven monotone
heap as store typing `Σ`, and treating a sig-violating heap mutation as a type `escape`
(same device as `co-semantics.md` §5.3). Two cheapest steps (gradual-guarantee `obs⁺` probe;
`srb`/`T.reveal_type` as a typing oracle) need no Lean. Its §C.5 records the *discipline*
decision (extrinsic typing + store typing `Σ` over the machine) and the Lean shape.

**Types (spec):** [Type judgments](type-judgments.md) — the implementation catalog for the
typing layer: every judgment form (`Ty`, `Sub`, `Consistent`/`≲`, `Join`, `mtype`, `narrow`,
`HasType`, `KontOk`/`ConfigTy`, `StoreOk`), the inference rules for the in-scope fragment
(one per `Expr` head, `send` being the whole game), the config/heap typing needed for a
machine-level preservation theorem, and a staging plan (T1 = the exact fragment already
proven in `Proof/Step.lean` → T2 send → T3 gradual boundary → T4 flow-sensitivity → T5+
generics). Companion to `types-and-preservation.md` (rationale) — this is the reference spec.

**Types (plan):** [Typed-portion safety](typed-portion-safety.md) — the plan of attack for
the property worth chasing: *a type error never occurs inside typed code* (the blame-theorem
shape), which unlike the whole-program statement already proved (L81) is non-vacuous on
partially typed codebases. Records the verified counterexample that makes the naive form
false (`untyped-boundary/002`: an unsigned callee's return crosses into a sig'd method
unchecked, and the TypeError fires *inside* the typed body while `srb` reports no errors),
the **call-graph closure** hypothesis it forces, the three kinds of callee that make closure
affordable (sig'd / RBI-declared builtin / unsigned — with RBI conformance becoming a
testable obligation rather than Sorbet's unchecked trust), the move of the bad state from
terminal outcome to configuration-at-raise, why runtime checks make the proof *local*
(per-method, sig as pre/postcondition, no global `Δ ⊨ H`), the erasure problem that makes
boundary checks shallower than the sigs, and milestones — M0 being "measure whether the
hypothesis is inhabited on real code, and abandon cheaply if not".

## Conventions

- **[V]** behavior verified against a real interpreter (CRuby 4.0.5, installed via
  Homebrew for this project); **[D]** sourced from documentation / ISO 30170; **[?]**
  open question to pin during mechanization, typically by differential testing.
- Small-step SOS over an explicit configuration; the inductive relation — not the
  interpreter — is the definition of record (PROJECT_PLAN §7).

## Central design bet

Everything is a message send (artifact 00 §4–5), and classes are ordinary heap objects
(artifact 01), so **one dispatch rule** (artifact 02 §3) carries the language and every
metaprogramming feature reduces to heap mutation (artifact 02 §6) — the property that
makes modeling Rails tractable.

## Not yet drafted (next artifacts)

- 07 — method invocation & parameter binding in full (splat/kwargs/block-arg normalization).
- 08 — the modeled core-library layer (Integer/String/Array/Hash builtins as primitive rules).
- 09 — metaprogramming operations (`define_method`, `*_eval`, `send`, hooks) as heap edits.
- 10 — the Rails vertical slice: ActiveSupport core-ext, mini-ActiveRecord (`method_missing`
  attributes + `belongs_to`/`has_many` macros), ActionController `before_action`.

Each is authored with [PROCEDURE-authoring-semantics.md](PROCEDURE-authoring-semantics.md)
and its `[V]` snippets become differential-testing cases per
[05-differential-testing.md](05-differential-testing.md) §7.
