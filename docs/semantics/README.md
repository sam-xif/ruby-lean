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
interpreter, and SUT executable live in [`../../ruby-lean/`](../../ruby-lean/README.md) (L0
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

**Design + as built (C0–C4):** [The certificate language](certificate-language.md) — type-checking as
**certificate replay**: the pivot back to `type-safety-by-reachability.md` §4/§6's
certifying-not-trusted architecture, now that the invariant machinery exists to receive
it. Generation (untrusted: solvers, RBI ingestion, LLMs) is decoupled from validation (a
search-free, kernel-`decide`d `validate` + a once-proved `validate_sound` through
`invariant_sound`); the certificate is the solved content of the assertion language
(`theta`/`deltaRows`/`bodies`/`ledger`/`assumes`), with residual assumptions first-class
in the conclusion. Design dimensions D1–D6 (stackmap-style join records, monomorphic
instantiations, boot schedules, Sorbet `static`/`guarded` row modes, a refutation
polarity, per-file linking) and milestones **C0–C9**, each with a gate and a ratchet —
the new fourth ratchet is *bodies certified-by-replayed-certificate*. **C0–C4 are built** and §9
is the as-built account: `validate_sound` is proved and axiom-clean, the fourth ratchet
stands at **11**, and the corrections the build forced are recorded there — a certificate
names the **declaration table** (so §3's anticipated bridging lemma is unnecessary),
`.fromDef` is unsound at `Machine.init p`, the kernel-replay cost is inherited from
`infer` rather than created, and the two rungs the measurements put **before C5** are R2
(name-global `declaresName`) and an `Assn` atom for a **constant**. The work is governed
by the `homebrew/PLAN.md` §4 norms (restated in §7) and **isolated in its own
directories** (`ruby-lean/RubyCore/Cert/` + `Proof/Cert/` trusted with V-numbers, top-level
`certify/` untrusted with E-numbers; import-only dependence on the existing trees).

**Design + BUILT through SF-T4 (extends the above):** [The slot frame](slot-frame.md) — local heap
stability as a first-order resource algebra (**SF-numbers**, 2026-08-28): the method
table as slot maps (`defined`/`empty`/`default`/`spine`) forming a PCM, a decidable
frame/conflict check over the certificate's footprint replacing the name-global
`declaresName` guard, `method_missing` as a write to the default component, boot
prefix outside the frame (`SemJudge`'s conformant start state). Priced against
[`../../homebrew/slice-inventory.md`](../../homebrew/slice-inventory.md), the
four-tier semantic-judgment inventory for typing the whole Homebrew slice with
bodies checked. **Built the same day** (`slot-frame.md` §10): the algebra and its
kernel `Bool` (`Types/SlotClaim.lean`), the install walk (`Types/SlotWalk.lean`),
SF-T1/SF-T2 + `holds_compose` + `row_lookupIn` (`Proof/Static/Frame.lean`,
axiom-clean), and the footprint riding `JCert` with `frameOkB` inside `validateJ`.
Still open: SF-T3's install-sets on `Judge` — until they land the frame is
*additive*, and `declaresName`'s name-globality cannot actually be removed.

**Plan (2026-08-30, sequences the two above):**
[Typing the slice — milestone plan](typing-the-slice-milestones.md) — the *machinery*
path from the measured baseline (**all six whole-file certificates carry zero rows**;
`sem_assumes` equals each file's `def self.x` count, so the accepts are real but never
look inside a body) to typed bodies. **M0 is the reordering finding**: the frame
half-breaks the layer's own semantic-judgment discipline — `SlotClaim.Holds` is a
*single-state* predicate and `frameOkB` conflates it with a claim about the program
text, so the property SF-T3 should prove is *defined nowhere*. Fix is a definition
(`SemFrame`, reachability-shaped like `SemJudge`, quantified over intermediate states
because a row is consumed at every dispatch) with `frameOkB` demoted to one of four
admission routes. **M0a** is the cheap one found by censusing all eight files: the only AST head in the slice with no rung in any plan is `fwd` (argument forwarding), and it exists only because `class_sugar_strip.rb` expands `alias` into `def m(...) = n(...)` — no slice source contains `(...)`; the rule that falls out is *a strip transform may only emit heads that already have a rung, else gate*. Then M1 metaclass hygiene (two real model defects found while
measuring), M2 qualified names pinning ids, M3 `srows` (`slice-verdict.md` §4a rung 3,
designed but unbuilt), M4 `self` at `.clsOf` in a `defs` body (the J11 widening), M5
the eigenclass-aware install walk (26/26 `opaque_` sites are `def self.x`), M6 dropping
name-globality, M7 the bodies. Interlocks with
[`../../homebrew/slice-inventory.md`](../../homebrew/slice-inventory.md), which prices
the *judgments* this sequences the machinery for.

**Design (amends the above):** [The judgment layer](judgment-layer.md) — the 2026-08-26
re-scoping of **C-1**: state the invariant over an **inductive judgment** (`Judge`/
`KJudge`/`MachineTyped`, transcribing `type-judgments.md` §6–§8 into Lean as the
definition of record) rather than over `chk` — the diagnosis being that metatheory stated
over a *function* (`infer.induct`, then `chk.induct`) is re-incurred at every checker
rewrite, and the relation is the layer stable under implementation churn. Settles the
**semantic type notion** first: recursive knots tied by *names into a table `D`* (never
anonymous structural recursion — that's coinductive); slots as heap-conformance
invariants, not intrinsic structure; responds-to sets indexed by boot phase; **unions +
nil + narrowing** as the load-bearing grammar (they are what refute `aboutToTypeStick`).
Certificates become **derivations-as-data** checked by a trivial local rule-matcher
(constructor-mirroring, so `Deriv.check → Judge` is one easy induction) — the maximal
form of "validation is search-free." `chk` is demoted to the coverage tier; the
`chk_table_ret` rung is deliberately abandoned. Milestones **J0–J4**; honest costs: the
preservation mountain is unchanged, only its marginal cost structure improves.

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

**Control (findings, 2026-09-11):** [Answer-typed judgments](answer-typed-judgments.md) — one
root cause behind four separate walls hit in a single investigation: `Evals` keeps the
`.value` arm of `RunResult` and discards the other four, so every rule's semantic
obligation is vacuous on an escape. Records the measurements (stuck-freedom does *not*
follow from the value axis; `Judge.vasgn` proved on the second axis for 16 marginal lines;
`Judge.while'` proved modulo two jump conditions, one of which turns out **false**; Iris's
`wp_bind` proved **unavailable** for this machine; and a 49-continuation census showing
Ruby's void-value rule exempts five of the seven jump constructors and *neither* of the two
ordinary code produces), the prior-art consensus that **an escape belongs to the answer,
not the step** (Essence-of-Ruby's `r ::= v | [v]^t | wrong`, λ_JS, Wright–Felleisen,
CakeML's `Rval | Rerr`, monadic/algebraic effects, double-barrelled CPS, Hazel's
protocols), and what RubyCore already has versus the one line where it diverges. §5 is
explicit that `lean-model-sketch.md`'s rejections of big-step and of meta-level exceptions
both **stand** — the answer type is orthogonal to both. §6 prices the proposal honestly:
it is a re-statement of the judgment layer, not a patch.

**Control (work order, 2026-09-11):** [The answer-typed schema](answer-typed-schema.md) — the
target shape for `ruby-lean/` and how to move it there, written to be handed to an agent. Seven
layers (certificate language → checker → `check_sound` → the answer-typed `SemJudgeA` →
adequacy → `CtlOk`/`KontOk`/`Inv` → safety), each with a working four-rule prototype to read
first (`ruby-lean/Denote/Proto/`, proved end to end). Carries an explicit **delete list** and a
migration in commit-sized steps, including the one step where the semantic ladder is
*restated* rather than climbed and how to report that honestly. Adds two norms to the standing
set: **state the general version of every theorem** unless a named requirement prevents it (the
prototype's adequacy was written at `Γ = []` and was useless for the only job adequacy has —
generalising it changed no proof), and **do not be married to existing code; delete dead code
liberally**, distinguishing *superseded* (delete) from *refuted* (keep the counterexample).
§7 lists the named gaps — `UncaughtInv`, the protocol-indexed frame rule, `catchK`'s missing
corpus rung, and the six of thirty-six continuation frames that correspond to no derivation
position — and §9 the four temptations that have already been tried and measured.

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
partially typed codebases. Records **four verified channels** by which untyped data reaches
typed code (`untyped-boundary/002`–`005`) — only one of which is a call, and one of which
(alias + mutate) shows that *no entry check, however deep, suffices* — and concludes that
the required condition is a property of the **heap over time**, not of the call graph: a
rely-guarantee condition that can be specified locally but not discharged locally. Takes the
**assume-guarantee** route (state it precisely, prove conditionally, *measure* it by taint
tracking in the model), and replaces the earlier `T.reveal_type` validation plan with a
**one-directional difftest** of a decision procedure `C` against `srb` (`C` accepts ⇒ `srb`
accepts — soundness is proved, so the test buys *relevance*), with a four-valued verdict
taxonomy in which `reject-witnessed` is the one verdict allowed to disagree, because a
replayable trace against an `srb`-accepted program *is* the finding. M0 is taint tracking,
deliberately first, as the cheap off-ramp.

**Types (POC, active):** [Static soundness on the fully-typed fragment](static-soundness-poc.md)
— the *smallest* soundness result the architecture can produce end-to-end, sequenced
**before** `typed-portion-safety.md`. It is row 1 of that document's table, which dismissed
it for coverage; the reason to do it first is that it is the only target whose theorem is
**unconditional** (no `R1`/`R2`, no rely condition, no measured hypothesis). Shape: a total
executable `check : Expr → Verdict` (two-valued — `accept`/`unknown`, no `reject` yet) plus
`check_sound : check P = .accept → ∀ r, ReachableResult → ¬ typeStuck r`, proving the
*strong* bad state rather than `sorbetStuck`, since a fully-typed program's sig checks
cannot fire. The tractability idea is `I ≡ InFragment ∧ WellTyped` — a machine-level
restriction conjunct that discharges most `stepFn` branches by contradiction so typing work
happens only on admitted ones. Records the unavoidable cost the prelude forces (a **builtin
signature table**, i.e. RBI-conformance at step one, since `1 + 2` is a send), the two
load-bearing exclusions that keep the class table static, and P0–P4 with the ratchet. §7 is
the **checker difftest**, built and exercised: the naive guard `accept ⇒ srb accepts` was
*measured* to fire on 38% of its own accept population (7006 unreachable, 3002 bignum
literal), so the relation is refined asymmetrically rather than the ratchet weakened, and
the three pinned zeros — accept-vs-srb, reject-vs-srb, and accept-vs-CRuby, the last of
which tests the *model* rather than the checker — are each verified to fire.

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
