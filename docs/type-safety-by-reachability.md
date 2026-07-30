# Type safety as reachability — "type-checking" Ruby by executing its semantics

A design sketch for a **cool derived result** off the Lean semantics: treat a program as
"type-checked" iff **no execution path reaches a type error**, generate a concrete
counterexample (input + trace) when one exists, and treat any declared type annotations as
a *separate, secondary* conformance check. No new type system — the semantics *is* the
specification, and "typed" means "the bad-state set is unreachable."

Status: **core metatheorem landed (2026-07-19); the checker engine is future work.**
The Direction-B metatheorem of §4 (`invariant_sound`) and the Direction-A execution
certificate of §3 are now proved in Lean — see `ruby/lean/RubyCore/Proof/TypeSafety.lean`
(and `implementation-notes.md` L51). The key implementation decision: they are formulated
over the **full executable transition relation** `SmallStep m m' := stepFn m = .next m'`,
not the partial control-core inductive `Step` — a subset relation reaches fewer states, so
safety over it would not transfer, and formulating over `stepFn` is why the theorem already
applies to real programs (dispatch/classes/blocks), including the `q_learning_extended`
demo. What remains is the **untrusted search engine** that discovers an invariant `I` per
program (§4, §7) and the type-annotation conformance check (§5) — those are still design.
It reuses machinery this workspace already sketches — it is the
[`bounded-effect-checking.md`](bounded-effect-checking.md) engine with **the bad-state
predicate swapped** from "effect violates the manifest" to "configuration is type-stuck."
Read that doc first; this one only records the deltas.

Origin: a 2026-07-16 design conversation. Written to be picked up cold later.

---

## 1. The reframe: this is a safety property, not a type system

The claim "no execution path results in a type error" is a **reachability / safety
property** over the small-step machine (`RubyCore/Machine.lean`, `RubyCore/Interp.lean`):

> The set of **type-stuck outcomes** is unreachable from the program's initial
> configuration (`Machine.init`) under all inputs.

A conventional type system is a *conservative, compositional over-approximation* of exactly
this property. The proposal is to attack the property directly instead — sound where we can
prove it, witnessed where we can't. That trade is the whole point: Ruby's dispatch is
heap-dependent (metaprogramming mutates method tables), so a compositional type system must
either punt (Sorbet/RBS gradual) or lie; a semantics-driven checker can reason against the
*actual booted heap*.

Two sub-problems hide here and want **different tools** — do not conflate them:

- **Prove absence** (no path, all inputs, unbounded fuel) → needs an inductive invariant /
  abstract interpretation. Undecidable in general for Ruby; this is the "really type-checked"
  claim.
- **Find a witness** (an input + trace reaching a type-stuck outcome) → bounded search;
  this is the "generate a counterexample program trace" demo. Cheap, high-value, and where
  "counterexample generation" actually lives.

## 2. The bad-state predicate, grounded in the actual model

The model already gives us the predicate almost for free. `StepResult`
(`RubyCore/Interp.lean:20`) terminates a run in one of:

| Result | Meaning | Role here |
|---|---|---|
| `done v m` | normal termination | safe outcome |
| `uncaught exc m` | a raised exception escaped to toplevel | **candidate type error** (filter by `exc`'s class) |
| `unsupported reason` | out-of-fragment construct | **analyzability frontier → UNKNOWN** |
| `stuck msg` | model genuinely wedged | model bug (route to difftest ratchet) |

The user's three "type errors" map onto `uncaught` **filtered by exception class**:

1. **method not found** → `NoMethodError` (raised at dispatch miss — `RubyCore/Interp.lean`
   ~L405–426; note the vcall/fcall `NameError` ambiguity currently *gates* to `unsupported`).
2. **arity mismatch** → `ArgumentError` (raised at the call/`initialize` rules ~L304).
3. **intentional `TypeError`** (`2 + "3"`, coercion failures, `def` on an immediate) →
   `TypeError` — several sites, some currently `unsupported`-gated.

```
typeStuck (r : StepResult) : Prop :=
  ∃ exc m, r = .uncaught exc m ∧ classOf m exc ∈ typeErrorFamily
  -- typeErrorFamily = NoMethodError ∪ ArgumentError ∪ TypeError, closed under subclassing
```

### Load-bearing subtlety: raised ≠ stuck

The bad state is the **terminal `uncaught` outcome**, *not* the `raiseJ` transition. Ruby
idiom deliberately raises-and-rescues these (`respond_to?` fallbacks, `method_missing`,
duck-typing via `rescue NoMethodError`). A `NoMethodError` that a `rescue` catches is a
*type-safe* program. So:

- The property is about **reachable outcomes**, not intermediate control states — which
  slightly shifts the invariant formulation (§4): you reason about which `StepResult`s the
  run can terminate in, and `raiseJ`-in-flight is a perfectly fine transient state that the
  begin/rescue konts may consume.
- This is strictly more faithful than a type system, which cannot see that a raise is
  locally caught.

### The frontier is first-class

`unsupported` is not failure — it is "we did not model this, so we cannot say." Treated
conservatively (may do anything → may be type-stuck), it becomes the **UNKNOWN(frontier
report)** verdict of `bounded-effect-checking.md` §3, and the desugarer/interp
fragment-coverage ratchet *doubles as the checker's completeness metric*. Same three-valued
discipline; loud, never silent.

## 3. Direction A — witness generation (the demo). Self-certifying, zero proof.

The engine claims "input `x`, trace `τ`, reaches a type-stuck outcome." **The certificate
is the trace.** Replay `τ` concretely through the trusted fuel interpreter (`stepFn`) and
observe the `uncaught`-of-type-family outcome. No theorem, no SMT, no soundness burden —
a witness is confirmed by execution (the "backward direction discharged per-witness by
execution" of [`relating-language-and-substrate.md`](relating-language-and-substrate.md)).
False positives are impossible once replay confirms; a witness that replays in-model but not
in CRuby is a **model bug**, routed to the difftest ratchet.

Mechanism = the concolic engine of `bounded-effect-checking.md` §2, verbatim:

- **Concrete boot, symbolic inputs.** Run requires/class defs/metaprogramming concretely to
  settle the heap and method tables; symbolize only argv/stdin/env/file contents. Dispatch
  then resolves against the real booted heap — the only thing that makes Ruby dispatch
  tractable.
- **Fork on branches; SMT prunes.** At each dispatch/arity/coercion rule, emit
  `pathCondition ∧ (receiver can't respond to m ∨ arity mismatch ∨ operand types force
  TypeError)`. SAT → concrete witness input.
- **Bounds as dials** (fuel, path budget, input sizes, solver timeout) — the verified
  frontier, reported as part of every verdict.
- **Shrink** (delta-debug) then **confirm on real CRuby** before reporting.

For the cheapest possible first cut: **`Plausible`** (Lean's property-based tester, the
`SlimCheck` successor) over `run`/`stepFn` will find *shallow* witnesses with no SMT at all
— random inputs, automatic shrinking. Good for de-risking the predicate and catching the
easy cases; it will *not* find the witness that needs a specific deep interleaving. Wire it
up first regardless.

## 4. Direction B — verification ("really type-checked"). Certifying, not trusted.

Here the engine claims safety **for all inputs**. What convinces a *small verified checker*
without trusting the (fast, clever, buggy, extracted-OCaml/Rust) engine? An **inductive
invariant** `I : Machine → Prop` that the untrusted engine *discovers* (abstract
interpretation / IC3 / PDR / hand-supplied). The Lean-verified validator then discharges
three **local, checkable** conditions against the real `Step` relation:

```
Initiation:   I (Machine.init program)
Consecution:  ∀ m m', I m → Step m m' → I m'
Safety:       ∀ m, I m → ¬ aboutToTypeStick m
              -- no reachable config transitions straight into an uncaught type-family exc
```

And the payoff — a **one-time metatheorem about the semantics**, proved once in Lean, that
turns *any* such `I` into a guarantee:

```
theorem invariant_sound (I : Machine → Prop)
    (init : I (Machine.init program))
    (cons : ∀ m m', I m → Step m m' → I m')
    (safe : ∀ m, I m → ¬ aboutToTypeStick m) :
    ∀ r, Reachable (Machine.init program) r → ¬ typeStuck r
```

This is a short induction on the reflexive-transitive closure of `Step`. It says **nothing
about any checker** — it is pure metatheory. Per program, the untrusted engine emits some
concrete `I`; Lean only re-checks `init`/`cons`/`safe` for *that* `I`. **We never prove the
engine correct — we prove the rule that makes its output trustworthy, once, and demote the
engine to untrusted.** Finding `I` is the hard, undecidable, heuristic part (outside);
checking `I` is decidable and local (inside).

### What is now proved (2026-07-19)

`RubyCore/Proof/TypeSafety.lean` proves `invariant_sound` exactly as stated above, plus the
Direction-A execution certificate (`run_value_type_safe`). Crucially it is formulated over
the **full** relation `SmallStep m m' := stepFn m = .next m'` — so *no separate inductive
dispatch `Step` is required* for the metatheorem, and it already covers `send`/dispatch,
classes, blocks, begin/rescue: everything `stepFn` models. The earlier framing ("deferred
until dispatch `Step` is authored") assumed the theorem would range over the inductive
`Step`; ranging over `stepFn` instead is both sound (a subset relation would be unsound for
a *safety* claim) and immediately general. `RubyCore/Proof/Step.lean` (the inductive control
core, refreshed for `redo`/`dowhile`) and its `Step.sound` remain the idiomatic relational
"definition of record," bridged in by `Step.subset_smallStep`.

What is *still* missing is not the theorem but its **consumer**: an (untrusted) engine that,
per program, discovers a concrete inductive invariant `I` whose Consecution is dischargeable
— the abstract domain must track method tables (§4.2), and that is where dispatch, arity,
and `method_missing` (§7) make the *inference* hard. The trusted validator + `invariant_sound`
are done; finding `I` is the open, undecidable, heuristic part.

### The checkability constraint shapes the abstract domain

`cons` and `safe` quantify over all states, so to *check* them for a given `I` they must be
decidable or SMT-dischargeable. That forces the invariant language into a fixed abstract
domain rather than arbitrary Lean `Prop`. For Ruby the domain **must track the object model**
— which methods each reachable receiver responds to, ancestor chains, arities — because
"receiver responds to `m`" is a *heap* fact, mutated by `prepend`/`define_method`/reopening.
Consecution becomes: *every step preserves "every reachable receiver responds, at the right
arity, to every method sent to it."* This is the substantive obligation, and it is checkable
only if the domain is chosen to keep it so. Note the tie-in to `bounded-effect-checking.md`
§4.2: the **semantic heap-diff** (dispatch-relevant heap delta) is the same object-model
abstraction, reused for incrementality.

## 5. Type annotations as a *separate* check

The user's second point: annotations are secondary. Keep them fully decoupled.

- The reachability property above is **annotation-free** — it is the ground truth of "does
  this program ever hit a type error."
- A declared type (RBS-style, or inline) is then checked as **conformance against the same
  semantics**: does the observed/abstracted return- and argument-type behavior along all
  bounded/invariant-covered paths *refine* the declaration? A mismatch is not a type error
  in the program — it is a **spec-vs-behavior discrepancy**, reported distinctly.
- This inverts the usual dependency: behavior is primary and self-justifying; annotations
  are optional refinements checked *for agreement*, exactly as difftest checks the model for
  agreement with CRuby. Same "two things that should agree, report when they don't" shape
  used everywhere in this workspace.

## 6. Trust base and Lean's actual role

- **Trusted:** Lean kernel + the semantics (`Step`/`stepFn`, `typeStuck`, `Machine.init`) +
  `invariant_sound` + the tiny validator that evaluates `init`/`cons`/`safe`.
- **Untrusted:** the whole search/inference engine, abstract interpreter, heuristics.
- **`Plausible`** gives random witnesses in-Lean; there is **no native symbolic-execution /
  directed counterexample generator** in Lean — that is model-checking machinery you build
  on top (SMT-backed), not something Lean hands you.
- **SMT caveat.** If `cons` needs an SMT solver and you accept cvc5/z3's bare "valid," the
  solver re-enters the TCB. To keep it out, the solver must emit a **checkable proof**
  (Alethe/LFSC) that Lean replays (cf. `lean-smt`/proof reconstruction). That reconstruction
  is real, known-painful work — the honest cost of "fully outside the TCB" for Direction B.
  Direction A needs none of this (replay is the proof).

This is the same **certifying-not-trusted / PCC spectrum** as `user-stories.md` §5 and
`bounded-effect-checking.md` §5: **PCC for unbounded claims when a submitter supplies the
invariant; certified bounded search (Direction A) as the automatic floor when they don't.**
Two effort levels, one checker, one `invariant_sound`.

## 7. Honest hard parts (ranked)

1. **Dispatch is the invariant.** The whole difficulty is that the abstract domain must
   model method tables, and the `Step` rules for dispatch don't exist yet. Everything waits
   on that.
2. **Path explosion through dynamic dispatch** (shared with `bounded-effect-checking.md` §7)
   — receiver ambiguity multiplies paths; mitigated by concrete boot + summaries, still real.
3. **Symbolic strings** — Ruby is string-saturated; SMT string theory is brittle. Expect
   timeouts to dominate the UNKNOWN set in Direction A early.
4. **`method_missing` / `respond_to_missing?`** — a receiver that responds to *everything*
   collapses the "responds to `m`" abstraction; must be modeled explicitly or the invariant
   is vacuous/unsound.
5. **Model fidelity** — inherited from difftest; the ratchet is the permanent foundation.

## 8. Sequencing — what must exist before picking this up

Prerequisites — **all three now done** (2026-07-19, `RubyCore/Proof/TypeSafety.lean`),
which reorders the original plan: #3 did *not* have to wait on #1, because ranging the
metatheorem over `stepFn` (rather than the inductive `Step`) makes it dispatch-complete for
free.

1. ~~Dispatch/object-model rules authored as inductive `Step`~~ — **not required for
   `invariant_sound`** after all; it ranges over `stepFn` (which already dispatches). Still
   worthwhile as the relational "definition of record" (`Step.subset_smallStep` bridges it),
   and needed if you want to reason about dispatch *relationally* rather than via `stepFn`.
2. **`typeStuck` predicate** — done (`typeStuck`/`isTypeError`/`typeErrorFamily`,
   NoMethodError ∪ ArgumentError ∪ TypeError closed under `isA`). The `NameError`/
   `NoMethodError` `unsupported` gate is unchanged upstream; a bare `NameError` is simply
   not in the family, so genuine `NoMethodError` misses are visible.
3. **`invariant_sound` metatheorem** — done, over the RT-closure `Reaches` of `SmallStep`.

Cheap de-risking runnable *before* all that:

- ~~**`Plausible` witness demo (Direction A, shallow)**~~ — **DONE** (2026-07-28,
  `lean/RubyCore/Search/Random.lean`, impl-notes L58). Finds `nil_dispatch`'s witness with
  automatic shrinking; the control program yields no false positive; and it *provably misses*
  a needle behind a narrow guard even at 20x budget — which motivated the next item.
- ~~**Toy integer-only concolic stepper**~~ — **DONE** (2026-07-29, `ruby/concolic/`).
  Solves for that needle in 2 iterations. `typeStuck` is the bad-state predicate, so the
  "swap the predicate" thesis is demonstrated end to end. **The Lean semantics is the
  executor** (`lean/ConcolicMain.lean` emits branch decisions + the authoritative outcome),
  so the engine holds no method tables of its own; see `concolic/implementation-notes.md`
  K9 and the dataflow design in `ruby/docs/semantics/concolic-dataflow.md`.
- **Object-model abstract domain, off-Lean:** boot programs under CRuby, dump method tables
  by reflection, and prototype the "responds-to" abstraction + its heap-delta invalidation
  (shared with the §4.2 semantic heap-diff) before committing it to Lean.

The through-line: **the product is one checker; the Ruby semantics is its executor.** Type
safety, effect confinement, and semantic diff are three bad-state predicates over the same
engine — not three projects.

## 9. Candidate corpus — what to run this on

Two tiers: **hand-written toys** that fit *today's* fragment (the de-risking ladder), and
the **DRuby featured corpus** (real programs with documented type-error bugs) once builtin
coverage grows. The paper's arc is: prove the loop on toys → reproduce-and-beat DRuby on
real code.

### 9.0 Reality check — what "fits the fragment" means today

**Re-audited 2026-07-30 by probing the built model directly** — the 2026-07-16 assessment
this replaces was badly out of date, and several things it called blockers have shipped.
Method: run minimal snippets through `bin/export-json | rubycore` and read the gate.

**Now working** (previously listed as missing): **call-site keyword arguments** in every
form (required, defaults, `**h` double-splat, `**kwrest`, `Class.new(a: 3)`) — §10.2's "#1
construct blocker" is *resolved*; **block-driven Enumerable** for `each`, `map`, `inject`,
`each_with_index`, `max_by`/`min_by`, `sum`, `3.times {}`, `Hash#each`/`each_key`/
`each_value`; **the reflection predicates** `is_a?`/`kind_of?`/`instance_of?`/`respond_to?`
(§10.3 #5 — the correctness-critical ones for false-positive-free pruning);
**`attr_reader`/`attr_writer`/`attr_accessor`**; `Range` as a value (literals,
`first`/`last`, `[*1..3]`); plus the L2 object model, blocks/procs/lambdas,
`begin`/`rescue`/`ensure`, `super`/`zsuper`, eigenclasses, Float shortest-roundtrip
formatting, seeded MT19937 `Random`, and `Math`.

**Still gated**, ranked by the *actual* tier-0 gate histogram (582 gates; counts are
first-gate-hit, so unblocking one may reveal another behind it — an upper bound on gain,
not additive):

| Count | Gate | Character |
|---|---|---|
| 38 | string `eval` family | permanently out of scope (artifact 00 §6) |
| 36 | `defined?` | desugar-side, cheap (§10.2 #2) |
| 29 | `zsuper` param reconstruction | delicate |
| 28 | `Array#[]` slice `(start,len)` | trivial builtin |
| 25 / 18 | `Rational` / `Complex` | numeric tower |
| 21 | `Integer#times` (a form other than the working block call) | small |
| 17 / 16 | `Regexp` / `Struct` constants | large |
| 10 | `define_method` | the metaprogramming gate |
| 10 | `Array#any?` | Enumerable predicate family |

**The Enumerable gap is now specific, not structural:** the `iterK` iterator machinery
works; what is missing are particular bodies — `select`, `reject`, `find`/`detect`,
`sort_by`, `all?`/`any?`, `count {}`, `group_by`, `each_with_object`, `Integer#upto` — plus
**Range enumeration** (`each`/`map`/`to_a`/`include?`: the value exists but is not
iterable). Each reuses the existing machinery (a filter-style `IterKind` plus a couple of
new kinds), so these are low-risk increments rather than new mechanism.

Consequence — **the 2026-07-16 conclusion is reversed.** The toy ladder is no longer
fragment-limited (T1-T5 all fit, and T5 is proved in both directions), and "no program that
iterates a collection can run" is false. The remaining distance to the real corpus is a
*list of named builtins*, not a missing mechanism. Note that the biggest single wins
(`defined?`, `zsuper`, `Array#[]` slice) are **not** Enumerable methods, so drive the work
off the histogram rather than off this document's earlier guesses.

### 9.1 Tier 0 — hand-written toys (runnable as the fragment stands)

Each is a **safe/buggy pair**: the buggy version has exactly one reachable type-stuck
outcome (the agent must generate the witness trace, fix it, and re-prove safe); the safe
version is the verification-direction demo. Loops are `while`/recursion, not Enumerable, to
stay in-fragment. All three type-error categories are covered, plus the object-model case
that is the crux of the invariant.

| # | Program (≈LOC) | Category | The reachable type error | Exercises |
|---|---|---|---|---|
| **T1** | `int_recursion` (~15) | *(none — prove-safe)* | — factorial/fib via recursion + `if` + arithmetic | verification direction, hand-checkable invariant; the calibration baseline |
| **T2** | `nil_dispatch` (~20) | `NoMethodError` | a helper returns `Integer` or `nil` by input; caller does `x.succ` unconditionally → nil path raises | the canonical "undefined method for nil"; witness = the nil-triggering input |
| **T3** | `lambda_arity` (~20) | `ArgumentError` | `->(a,b){…}` (strict lambda) reached with one arg on some branch | arity as a type error; block/lambda arity semantics (L1) |
| **T4** | `coercion` (~20) | `TypeError` | a var is `Integer` on one path, `String` on another; then `n + 1` (or `"a" + n`) on the String path | coercion type errors — **gate check:** confirm the relevant `+`/coercion site raises vs. currently returns `.unsupported`; pick whichever operator is modeled |
| **T5** | `class_hierarchy` (~30) | `NoMethodError` | two subclasses, one lacks method `m`; receiver chosen by input; caller sends `m` | **method-table-dependent dispatch** — the exact thing the invariant domain must track; the most important toy |

T5 is the load-bearing one: it is the smallest program where "prove type-safe" *requires*
an invariant over the object model (which receivers respond to `m`), so it calibrates
whether an agent can synthesize that invariant (the real §7 unknown) before scaling. T4 has
a **prerequisite to verify first**: whether the model's arithmetic/coercion sites raise
`TypeError` in-model or currently gate to `.unsupported` (several coercion sites do — grep
`unsupported` in `Interp.lean`); if gated, T4 waits or picks a modeled operator.

Recommended order: **T1 → T5 → T2 → T3 → T4** — prove-safe first, then the object-model
invariant (the crux), then the three witness-generation categories.

### 9.2 Tier 0.5 — stdlib bridge (first *real* code, small)

Self-contained pure-Ruby stdlib classes: real, spec'd, dispatch-rich, used everywhere, and
each grows exactly the builtins the real corpus needs. Prioritize by fragment distance:

- **`Set`** (thin wrapper over `Hash`) and **`Prime`** — smallest; mostly need a few Hash/
  numeric builtins + iteration. First real "prove type-safe" targets.
- **`Comparable`/`Enumerable` mixin consumers** — once block-iteration lands, these validate
  the mixin-dispatch case (DRuby's `Ordered` example) against the object-model invariant.

### 9.3 Tier 1+ — the DRuby featured corpus (once builtins grow)

From Furr/Foster, *Static Type Inference for Ruby* (SAC'09), Fig. 1 — 18 programs, 29–1030
LOC, RubyForge. Reproducing this set gives precedent, representativeness, and a baseline to
beat (**DRuby: 5 errors / 16 warnings / 16 false positives** — our approach targets *zero*
false positives by construction, §1). Featured subset, ranked for the find→fix→prove loop:

| Program | LOC | Documented bug (DRuby §6.1) | Category | Availability / gap |
|---|---|---|---|---|
| **ObjectGraph** | 153 | `break k` from `each_object` returns `Class`; normal exit returns `Fixnum` → input-dependent downstream `NoMethodError` | union-by-control-flow | RubyForge archive; **best full-loop demo** (bug is input-triggered) |
| **hashslice** | 91 | `@hash['a','b'] = 3, 4` parses as 3 args → arity error masked by coercion | arity + parse-disambiguation | RubyForge archive; smallest real bug |
| **vimrecover** | 173 | two undefined vars in error-recovery branches | undefined-var (`NameError`) | RubyForge archive |
| **ai4r** | 992 | `return rule_not_found if …` — undefined var on a branch the program's *own tests never hit* | undefined-var | **live**, maintained, no deps, algorithmic → fragment-friendlier; flagship |
| **StreetAddress** | 877 | *(no error found; prove-safe)* | — | **live** (`street-address-rb`); regex-heavy → Tier 3 |
| **text-highlight** | 1030 | *(metaprogramming via `eval`; DRuby punted)* | out-of-fragment | shows the frontier honestly (`unsupported`/UNKNOWN) |

Prove-safe subset (DRuby 0/0/0), good for the verification direction + certificate demo:
`pscan` (29), `merge-bibtex` (103), `style-check` (150), `gs_phone` (827).

**Sourcing:** `ai4r` → [github.com/SergioFierens/ai4r](https://github.com/SergioFierens/ai4r);
`StreetAddress` → [github.com/street-address-rb/street-address](https://github.com/street-address-rb/street-address);
the RubyForge-only programs → [devrandom/rubyforge mirror](https://github.com/devrandom/rubyforge)
+ Internet Archive. The companion **OOPSLA'09** paper ("Profile-Guided Static Typing")
carries a larger benchmark set to mine for bigger targets.

**Fragment gap for this tier:** all of it needs Enumerable iteration; the parsers
(`StreetAddress`, `text-highlight`, `style-check`) additionally need regex; none need Rails.
So the ratchet target after Tier 0.5 is **Enumerable-with-blocks first, regex second** —
which is what unlocks `ai4r` (the flagship) without paying for regex.

## 10. Constructs to model + the mocking approach

Grounded in an audit (2026-07-16) of `Syntax.lean`/`Builtins.lean`/`desugar.rb` against
`ai4r` (`data_set.rb`, `k_means.rb`) and the stdlib bridge targets. **Key finding: the gap
is overwhelmingly builtin-method *semantics*, not AST constructs** — most of what real code
needs already decodes.

### 10.1 Already present (do not re-plan)

**(Updated 2026-07-30 — see the §9.0 re-audit for the verified list.)** Also already present
and NOT to be re-planned: **call-site kwargs** (all forms), the **reflection predicates**
(`is_a?`/`kind_of?`/`instance_of?`/`respond_to?`), **`attr_*`**, and block-driven `each`/
`map`/`inject`/`each_with_index`/`max_by`/`min_by`/`sum`/`times`/`Hash#each`.

`case/when` (desugared, `desugar.rb:306`); structured params incl. keyword/optional/
destructuring (M2 — `req`/`opt`/`key`/`kwrest`/`block`/`fwd`/`destr`); blocks/`yield`/`->`;
`for`/`while`/`dowhile`; `begin`/`rescue`/`ensure`/`retry`; class/module/singleton/`super`.
Arithmetic **and its type errors** are modeled: `Array#+` with a non-array raises `TypeError`
("no implicit conversion of X into Array"); `1 < "a"` raises `ArgumentError` ("comparison of
Integer with String failed"). **Consequence: T4 (coercion `TypeError`) is viable today** —
use `Array#+`/`Array#-` with a wrong-typed operand, or `<` across types; no need to wait on a
new coercion site.

### 10.2 Construct-level gaps (small, ranked)

1. ~~**Call-site keyword arguments**~~ — **DONE** (verified 2026-07-30: required, defaults,
   `**h`, `**kwrest`, `Class.new(a: v)` all run). No longer a blocker.
2. **`defined?`** — still gated; **now the single largest actionable gate (36 tier-0 cases)**.
   Needed for `@x ||= …` / `CONST ||= …` and some guards. Desugar-side and cheap: do it first.
3. **Argument forwarding `...`** (`pfwd`/`fwd`) — gated; rare in this corpus.
4. `case/in` pattern matching — deferred (unrelated to `case/when`, which works).

### 10.3 Builtin-semantics gaps (the real work, ranked)

**(Rewritten 2026-07-30 against the measured gate histogram; the previous list's items 1–3
and 5 are substantially or fully done — see §9.0.)**

1. **The Enumerable *predicate* family** — `select`, `reject`, `find`/`detect`, `all?`/`any?`,
   `count {}`, `sort_by`, `group_by`, `each_with_object`, `Integer#upto`. The `iterK`
   machinery and the collect/fold/maxBy kinds already exist, so these are new `IterKind`s +
   bodies, not new mechanism. (`all?`/`any?` double as pruning predicates.)
2. **`Range` enumeration** — `each`/`map`/`to_a`/`include?`/`sum`. The value exists (L48) and
   `spread` already expands integer ranges, so this likely routes through the same iterator.
3. **`Array#[]` slice `(start, len)`** — 28 tier-0 cases for a trivial builtin; take it early.
4. **Array/Hash/Float completeness** — `Array.new(n){…}`, `dup`, `round`, hash `sort_by`.
5. ~~**Complete the reflection predicates**~~ — **DONE** (`is_a?`/`kind_of?`/`instance_of?`/
   `respond_to?` all verified working 2026-07-30). The precision argument below still stands
   and is now *realized*, not aspirational.
6. **Bigger, separate efforts:** `zsuper` param reconstruction (29), the numeric tower
   (`Rational`/`Complex`, 43 combined), `Struct`, `Regexp`, and `define_method` (10 — the
   metaprogramming gate, and the one that most matters for the concolic story).

**Precision insight — why #5 is correctness-critical, not coverage.** DRuby's 16 false
positives came from *union types discriminated by runtime tests* (§9.3). A program that
guards `x.foo if x.respond_to?(:foo)` or `return unless x.is_a?(Array)` is **safe**, and
because the checker *executes the real predicate*, the path-sensitive search prunes the
impossible branch for free — occurrence typing without occurrence-typing machinery. Faithful
`is_a?`/`respond_to?` is what cashes out "zero false positives by construction" (§1). Treat
as correctness-critical.

**Build order (revised 2026-07-30, histogram-driven):** `Array#[]` slice → `defined?`
(10.2 #2) → the Enumerable predicate family (10.3 #1) → `Range` enumeration → `zsuper` param
shapes → Array/Hash fill-in. The first three are ~90+ tier-0 cases and low risk; that
sequence still reaches `ai4r` without touching regex. Re-measure the histogram after each
batch (`difftest run --tier 0 --sut lean`, then read `cases.jsonl`) rather than trusting this
list — it is a snapshot, and counts are first-gate-hit so unblocking one reason can reveal
another behind it.

### 10.4 Mocking dependencies

For this phase, dependencies are **mocked, not modeled**. Central principle: **a mock is
heap pre-population, not a new evaluation rule.** `Boot.initHeap` already installs builtin
classes as ordinary heap objects with method tables; a mock is just more such objects,
installed before `Machine.init`. Minimal new semantics: an `installMocks : Manifest → Heap →
Heap` and a `require` builtin arm.

**`require` vs `require_relative`:**
- `require_relative "x"` → an **internal corpus file** → *load and desugar it for real* (it
  is the code under test; ai4r's `statistics`/`data_set`/`proximity` are the algorithm).
- `require "gem"` → consult the **mock manifest**, install the mocked class(es), return true.
  Unknown target → `.unsupported` (frontier, conservative).

**Three fidelity levels** (matched to checker needs; L2/L3 *are* the mediator `M` / effect
interface `E` of [`relating-language-and-substrate.md`](relating-language-and-substrate.md)
and [`bounded-effect-checking.md`](bounded-effect-checking.md) — mocking instantiates that
architecture, it does not fork it):

| Level | What | Trust | Lean impact |
|---|---|---|---|
| **L1 — in-fragment stub** | dep re-implemented in real RubyCore (`Set` as a Hash wrapper — how stdlib does it; a 10-line `statistics`) | **checked, not trusted** — zero trust gap | none; just more user code |
| **L2 — typed opaque stub** | method returns a fresh *symbolic value of a declared type*; contract at the seam (DRuby `base_types.rb`, executable + dynamically checked) | **trusted annotation**; blame localizes at boundary; confirmed per-witness by replay vs. the real gem | one new value form (opaque/typed) — a *concolic-layer* concept; base stepper gates on concrete inspection |
| **L3 — effect-labeled mock** | IO/nondeterminism (`File`, `CSV.foreach`, `Random`, `Marshal`) emits an **effect label** + returns a typed/symbolic result | trusted seam = effect interface `E` | reuses the effect machinery |

**Concrete `ai4r` mapping:** `require 'set'` → **L1**; `require_relative
'statistics'/'data_set'/'proximity'` → **load for real**; `Marshal.load(Marshal.dump(x))`
(deep copy) → a small **real builtin** (heap-subgraph clone — pure, well-defined);
`require 'csv'`/`CSV.foreach` → **L3** (iterate a fixed/symbolic array of typed rows);
`Random.new(seed)`/`@rng.rand` → **L3** (symbolic for soundness, concrete-PRNG replay to
reproduce a witness).

**Trust & diffability:** the mock manifest is diffable text like the effect manifest — an
L2/L3 entry is an explicit, reviewable assertion "the real gem behaves like this," so
"mock it out" never silently becomes "trust everything." L1 mocks do not expand the TCB.
**Phase recommendation:** L1 for pure stdlib-ish deps, L2 opaque-typed for the rest,
load-for-real on `require_relative` — so the *actual algorithm code where the type bugs live
executes for real* while CSV/Random/Marshal are mocked at a diffable seam.
