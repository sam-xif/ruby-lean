# RubyCore Semantics — 6: `desugar` and How We Build Trust in It First

> Notation: `00-notation-and-syntax.md` (esp. §4 the RubyCore grammar, §5 the desugaring
> table). Methodology base: `05-differential-testing.md`. Playbook: `PROCEDURE-authoring-semantics.md`.

This artifact specifies the front end — `desugar : Surface → RubyCore` — and, crucially,
**how we earn trust in it *before* giving RubyCore any semantics.** The ordering is
deliberate (per the project discussion): a solid, behavior-preserving front end is a
prerequisite for the model, and it can be validated on its own.

---

## 1. Why `desugar` can be tested with no RubyCore semantics

`desugar` is a **source-to-source, behavior-preserving** transform, so its correctness is
checkable entirely inside Ruby. With a RubyCore pretty-printer `render_core : RubyCore →
Ruby` and the trivial surface printer `render_surf : Surface → Ruby`, the defining
property is a **metamorphic round-trip** (claim C2 of artifact 05 §1):

```
  ∀ surface program s in the modeled fragment:
        obs_ruby( render_surf(s) )   ≡   obs_ruby( render_core(desugar(s)) )
```

Both sides run through **CRuby only** — no RubyCore interpreter exists yet, and none is
needed. This is the whole reason we can front-load desugar testing.

Two structural checks are *pure* (no oracle, run on every `desugar` output):

- **Well-formedness** — `is_core(desugar(s)) = true`: the output uses only RubyCore forms
  (artifact 00 §4), no residual sugar. Catches "forgot to handle this node."
- **Normal form / idempotence** — `desugar(reparse(render_core(desugar(s))))` is
  structurally equal to `desugar(s)`. Catches unstable or non-terminating rewrites.

### Trusted-base caveat

The round-trip validates `render_core ∘ desugar` *as a pair*; a compensating bug (desugar
breaks X, render un-breaks it) would hide. Mitigations: keep `render_core` near-identity
(RubyCore is deliberately Ruby-shaped); test it independently via structural round-trip
`reparse(render_core(x)) ≅ x`; and rely on the two pure checks above, which don't involve
`render_core` on the surface side.

---

## 2. What we observe: value **and evaluation order**

Value-only comparison misses the most important class of desugaring bugs — the ordering
and once-only-evaluation obligations that desugaring exists to make explicit (the RIL
linearization concern; see artifact 00 §5). `a.b ||= c` must evaluate receiver `a`
**exactly once**; a buggy desugaring that evaluates it twice can still return the same
value.

So for desugar testing we **extend `obs` (artifact 00 §2) with a side-effect trace**:

```
  obs⁺(program) = ( obs(program) , trace )
  trace = the ordered log of observable markers evaluated, with multiplicity
```

Test programs are generated (or instrumented) so that subexpressions call an observable
marker (append a tag to a global log). Two programs agree under the round-trip **iff they
evaluate the same markers in the same order the same number of times**. This is the cheap
mechanism that catches receiver-evaluated-twice, operand-reordering, and short-circuit
bugs that a value-only oracle waves through.

---

## 3. The reframe: "nonsensical" is fine, "shallow" is the enemy

For desugar testing, a program that deterministically raises (e.g. `NoMethodError`) is a
**perfectly good oracle case** — desugar must preserve that exact observation. The bar is
only:

1. **parseable**, and
2. **deterministic** under CRuby (terminates; no clock/RNG/thread/GC-observable nondeterminism).

(1) is free if we **generate at the AST level** and render to source, because `desugar`
operates on the parsed (prism) AST anyway — surface syntactic variety has already
collapsed at parse time, so it is the *parser's* concern, not desugar's. (2) is handled by
CRuby-as-filter + not generating `Time`/`rand`/threads (artifact 05 §3.2, §4.1).

The residual risk is not nonsense but **shallowness**: a generator that mostly emits
`undefined method`/`undefined local variable` programs produces valid-but-trivial cases
that bail at line 1 and never exercise desugar on rich, *nested* constructs. Defeating
shallowness is the job of the three-pronged corpus below.

---

## 4. The three-pronged corpus

The prongs are complementary along distinct axes; no single one suffices.

| Prong | Nature | Strength | Weakness | Role |
|-------|--------|----------|----------|------|
| **1. `bootstraptest/`** | curated, real, human-written | high signal; core-language-focused; genuinely self-contained; ships an oracle value | **small** volume | regression base; `obs` cross-check; seeds for prong 2 |
| **2. Superion-style grammar-aware fuzzing** | broad, random, structure-aware | volume; unexpected *combinations* of rules | shallow/uninteresting without care | breadth; find rule interactions we didn't think of |
| **3. AI-agent targeted examples** | intentional, adversarial | reaches semantic corners requiring *understanding* | doesn't scale to volume | precision; kill the subtle obligations |

### Prong 1 — MRI `bootstraptest/`

CRuby's pre-build smoke suite: each test is `assert_equal '<expected>', '<program>'` where
the program string is **complete and self-contained** (no `require`, no framework object
graph, no cross-block setup). We do **not** run its harness; we parse the test files and
*lift out the program strings*. Notes:

- It is core-language/VM-focused — exactly desugar's target fragment.
- The `expected` first argument is a **free cross-check on our `obs` normalizer** (artifact
  05 §3.2): if `obs_ruby(program)` disagrees with bootstraptest's expected string, our
  observation function — not desugar — is suspect.
- Filter out tests probing out-of-scope behavior: GC/`ObjectSpace`, threads/`Ractor`,
  deliberate `SyntaxError` cases, VM internals (artifact 00 §6, PROJECT_PLAN §4).
- **Why not `ruby/spec` or MRI `test/`?** Those run on **mspec** / **minitest** — a bespoke
  harness and a bundled *library*, respectively; **neither is part of the language**, and
  their example bodies are coupled to `describe`/`before`/`let` setup, so they are not
  self-contained. Harvesting them is deferred (artifact 05 §4); the frameworks stay out of
  the model.

### Prong 2 — Superion-style grammar-aware fuzzing

Structure-aware, coverage-guided mutation (Wang et al., ICSE'19; see artifact 05 §2 and
§4.1). Concretely:

- **Seeds** = prong-1 programs + the desugaring examples of artifact 00 §5. Real,
  in-scope seeds make mutants far more sensible than de-novo generation.
- **Mutation** = AST-subtree splicing between seeds (Superion's core move), plus
  scope-aware generative fill (below).
- **Scope-aware generation** to defeat shallowness — the Csmith analogue: maintain an
  environment during top-down generation and only reference bound names (only read `x`
  after binding `x`; only call/reference `def`'d methods / assigned constants, or restrict
  sends to a known-safe core vocabulary with known arity). Optional lightweight
  literal-type tracking (Integer vs String) so operator sends land on plausible receivers
  and programs run *deeper*.
- **Guidance** = desugaring-rule coverage (§5): steer toward untouched rules and untested
  rule *pairs*.

### Prong 3 — AI-agent targeted examples

An agent (following `PROCEDURE-authoring-semantics.md`) that *reads the desugaring table*
and writes programs deliberately stressing each rule's semantic obligation — the corners
random generation is unlikely to hit and curated suites happen to miss. Each example uses
the evaluation-order trace (§2). Priority targets:

- `x ||= e` / `a.b ||= c` / `h[k] ||= v` — receiver/key evaluated **once**; local-var
  creation semantics of `||=` on an undefined `x`.
- `&.` safe navigation — receiver once, nil short-circuit skips the call *and* its args.
- string interpolation — `to_s` dispatch and strict left-to-right order.
- multiple assignment / splat (`a, *b, c = …`; `a.m, b[i] = …`) — a notorious desugaring.
- `case/when` — subject evaluated once; `===` dispatch order across `when`s; `else`.
- operator precedence / associativity with side-effecting operands (`f() + g() * h()`).
- `for … in` → `each` block (variable leaks to enclosing scope, unlike block params!).
- `&&`/`||`/`and`/`or` value-preservation (they return an operand, not a boolean).

The agent is **steered by coverage holes** (§5): after prongs 1–2 run, it is pointed at
the rules and rule-pairs still uncovered or under-covered.

---

## 5. Metric: desugaring-rule coverage

Instrument `desugar` to emit the set of **rewrite rules fired** per input (and, more
valuably, the set of rule *pairs* co-firing — interpolation-inside-a-rescue-inside-a-block).
Aggregate over the whole corpus. This is the desugar-level analogue of the semantic-rule
coverage of artifact 05 §6:

- An uncovered rule is either dead (front-end bug) or untested (→ point prong 3 at it).
- Rule-**pair** coverage is the real target: desugaring bugs cluster at *interactions*
  (an `||=` whose RHS is a `case`, a splat inside a multiple-assignment inside a block).
- Coverage feeds back into prong 2 (bias generation) and prong 3 (agent targets).

---

## 6. Disagreement triage (simpler than the full model pipeline)

Because RubyCore has no semantics yet, the only components under test are `desugar`,
`render_core`, and the `obs` normalizer. So the artifact 05 §5 pipeline collapses to:

```
  round-trip disagreement (obs⁺ differs)
     │  minimize (structure-aware reducer / shrinkray, artifact 05 §5)
     ▼
     ├─ differs only in a normalized field / vs bootstraptest expected → OBS-NORMALIZER bug (fix §3.2)
     ├─ trace differs (order/multiplicity)                             → DESUGAR bug: broke evaluation order/once-only
     ├─ value/exc differs                                             → DESUGAR bug: changed meaning
     ├─ render_core(x) alone misparses / structural round-trip fails   → RENDER bug (fix the printer)
     └─ program uses an out-of-fragment feature                       → OUT OF SCOPE → filter it out
```

No "model bug" bucket exists yet — that's the point of doing this round first.

---

## 7. Exit criterion — when do we trust `desugar` enough to move on?

Move to building RubyCore semantics when **all** hold:

- [ ] 100% round-trip agreement (`obs⁺`) on the filtered bootstraptest corpus, and the
      bootstraptest `expected` cross-check passes (validates `obs` too).
- [ ] Desugaring-rule coverage saturated; every rule and every *reachable* rule-pair
      exercised by at least one passing case.
- [ ] Prong-2 fuzzing runs to a stable low disagreement rate (trending to zero), with all
      minimized disagreements triaged and fixed or documented as out-of-fragment.
- [ ] The prong-3 adversarial obligation list (§4.3) all pass under the trace-augmented
      observation.
- [ ] Pure checks (`is_core`, normal-form) hold on the entire corpus.

At that point `desugar` is a trusted front end, and RubyCore semantics can be built and
tested (claim C1) against a fixed target — with any future C1 disagreement known *not* to
be a front-end artifact.

---

## 8. Open questions

- **[?]** How faithful must `render_core` be to keep the trusted base small? Could we skip
  `render_core` by defining `desugar` to emit an AST that CRuby's own `prism` can
  *unparse*, reusing a maintained unparser instead of writing our own?
- **[?]** Semantics-aware shrink moves (artifact 05 §7): which AST reductions preserve
  parseability *and* trace-observability enough to hand to shrinkray?
- **[?]** Does scope-aware generation bias us away from the very `NameError`/`NoMethodError`
  paths that exercise `method_missing`-relevant desugarings? May need a deliberate
  "undefined-reference" generation mode.
- **[?]** Fragment boundary: some surface forms desugar into RubyCore *plus* a library
  call (e.g. `for`/`case` lean on `each`/`===`). Are those in-fragment for desugar testing,
  or do they need the library layer (artifact 08) to be even runnable? (They are runnable
  under CRuby regardless — the question is whether a divergence implicates desugar or the
  library.)
