# The round-trip method (artifact 06)

Why the front end can be validated before RubyCore has any semantics, and what that
validation has to observe. Code comments cite this page as *"artifact 06 §N"*; the
section numbering is kept stable for that reason.

The short version: for a program `P`, check that `P` and
`render_core(desugar(parse(P)))` produce the same observation under CRuby, where the
observation includes an evaluation-order trace as well as the final value.

```
  P ──parse──▶ Prism AST ──desugar──▶ RubyCore ──render_core──▶ Ruby′
  obs⁺_CRuby(P)   ≟   obs⁺_CRuby(Ruby′)      (+ pure checks: is_core, normal-form)
```

## 06 §1 — Why `desugar` can be tested with no RubyCore semantics

`desugar` is a **source-to-source, behavior-preserving** transform, so its
correctness is checkable entirely inside Ruby. With a RubyCore pretty-printer
`render_core` and the trivial surface printer `render_surf`, the defining
property is a **metamorphic round-trip**:

```
  ∀ surface program s in the fragment:
     obs_ruby( render_surf(s) )  ≡  obs_ruby( render_core(desugar(s)) )
```

Both sides run through **CRuby only.** That is the whole reason desugar testing
could be front-loaded: a solid front end is a prerequisite for the model, and
waiting for the model to validate it would have inverted the dependency.

Two structural checks are *pure* — no oracle, run on every output:

- **well-formedness** — `is_core(desugar(s))`: the output uses only RubyCore
  forms, no residual sugar. Catches "forgot to handle this node."
- **normal form** — `desugar(reparse(render_core(desugar(s))))` is structurally
  equal to `desugar(s)`. Catches unstable or non-terminating rewrites.

**Trusted-base caveat, stated rather than hidden.** The round-trip validates
`render_core ∘ desugar` *as a pair*; a compensating bug (desugar breaks X, render
un-breaks it) would hide. Mitigations: keep `render_core` near-identity — RubyCore
is deliberately Ruby-shaped — test it independently via the structural round-trip,
and lean on the two pure checks above, which do not involve `render_core` on the
surface side.

## 06 §2 — Observe the value **and the evaluation order**

Value-only comparison misses the most important class of desugaring bugs: the
ordering and once-only obligations that desugaring exists to make explicit.
`a.b ||= c` must evaluate the receiver `a` **exactly once**; a desugaring that
evaluates it twice can still return the same value.

So the observation is extended with a side-effect trace:

```
  obs⁺(program) = ( obs(program) , trace )
  trace = the ordered log of observable markers evaluated, with multiplicity
```

Two programs agree **iff they evaluate the same markers in the same order the
same number of times.** This is the cheap mechanism that catches
receiver-evaluated-twice, operand reordering, and short-circuit bugs that a
value-only oracle waves through — see the `--bug` demo in [Growing the fragment](growing-the-fragment.md).

## 06 §3 — "Nonsensical" is fine; "shallow" is the enemy

A program that deterministically raises `NoMethodError` is a **perfectly good
oracle case** — desugar must preserve that exact observation. The bar is only:
**parseable**, and **deterministic** under CRuby.

Parseability is nearly free because generation happens at the AST level and
renders to source — surface syntactic variety has already collapsed at parse
time, so it is the *parser's* concern, not desugar's.

The residual risk is not nonsense but **shallowness**: a generator that mostly
emits "undefined method"/"undefined local variable" programs produces
valid-but-trivial cases that bail at line 1 and never exercise desugar on rich,
*nested* constructs. Defeating shallowness is the job of the corpus below.

## 06 §4 — The three-pronged corpus

Complementary along distinct axes; no single prong suffices.

| Prong | Nature | Strength | Weakness |
|---|---|---|---|
| **1. `bootstraptest`** | curated, real, human-written | high signal, core-focused, self-contained, *ships an oracle value* | small volume |
| **2. grammar-aware fuzzing** | broad, random, structure-aware | volume; unexpected rule *combinations* | shallow without care |
| **3. adversarial targeted examples** | intentional | reaches corners requiring *understanding* | doesn't scale to volume |

**Prong 1 — MRI `bootstraptest`.** CRuby's pre-build smoke suite: each test is
`assert_equal '<expected>', '<program>'` where the program string is complete and
self-contained. The harness is not run; the test files are parsed and the program
strings lifted out (`bin/harvest_bootstraptest`). The `expected` argument is a
**free cross-check on the `obs` normalizer** — if `obs_ruby(program)` disagrees
with it, the observation function is the suspect, not desugar. Tests probing
GC/`ObjectSpace`, threads, deliberate `SyntaxError` or VM internals are filtered
out.

Why not `ruby/spec` or MRI `test/`? Those run on **mspec** and **minitest** — a
bespoke harness and a bundled library. Neither is part of the language, and their
example bodies are coupled to `describe`/`before`/`let` setup, so they are not
self-contained. Deferred, and the frameworks stay out of the model.

**Prong 2 — grammar-aware fuzzing.** Built, as the difftest engine's
[tier 1](../testing/engine.md#the-tiers). Two findings from designing it are worth keeping.
First, the approach chosen was *generate a surface AST and render it to Ruby text*
rather than Superion's splice-a-parsed-tree, because **Prism has no unparser** and
`render_core` handles only RubyCore, i.e. post-desugar — so mutation of scraped
Ruby stayed deferred while generation did not. Second, generation is
**scope-aware**: an environment threads through so only bound names are
referenced, which is the single highest-leverage feature, because a naive
generator produces valid-but-shallow programs that die at line 1 with `NameError`
and never reach nested sugar.

Its honest ceiling, stated when it was designed and still true: prong 2 excels at
breadth and at rule *combinations*, and shakes out crashes on valid-but-weird
trees — but because `desugar` is mostly structural, the subtle semantic
obligations (once-only evaluation, ordering) are better hit by prong 3. It
complements prong 3 rather than replacing it.

**Prong 3 — adversarial targeted examples.** Programs written deliberately to
stress each rule's semantic obligation, each using the evaluation-order trace.
The standing obligation list: `x ||= e` / `a.b ||= c` / `h[k] ||= v` (receiver and
key evaluated **once**); `&.` (receiver once, nil short-circuit skips the call
*and* its arguments); interpolation (`to_s` dispatch, strict left-to-right);
multiple assignment and splat; `case/when` (subject once, `===` dispatch order);
precedence and associativity with side-effecting operands; `for … in` (the index
leaks to the enclosing scope, unlike block params); and `&&`/`||`/`and`/`or`
value-preservation — they return an *operand*, not a boolean. Realized as tier 3.

## 06 §5 — Metric: desugaring-rule coverage

`desugar` emits the set of rewrite rules fired per input, aggregated over the
corpus (`bin/run` reports it). The analogue of semantic-rule coverage
([artifact 05 §6](../testing/methodology.md#05-6-metrics)).

An uncovered rule is either dead (front-end bug) or untested (→ point prong 3 at
it). **Rule-*pair* coverage is the real target**: desugaring bugs cluster at
interactions — an `||=` whose RHS is a `case`, a splat inside a multiple
assignment inside a block. Coverage feeds back into prong 2 (bias generation) and
prong 3 (choose targets).

## 06 §6 — Triage

Because RubyCore had no semantics when this was built, the only components under
test are `desugar`, `render_core` and the `obs` normalizer, so the full
disagreement pipeline collapses to four buckets:

| Symptom | Bucket |
|---|---|
| differs only in a normalized field, or against bootstraptest's `expected` | **obs_normalizer** |
| the *trace* differs (order or multiplicity) | **desugar** — broke evaluation order / once-only |
| the value or exception differs | **desugar** — changed meaning |
| `render_core(x)` misparses, or the structural round-trip fails | **render** — printer bug |
| the program uses an out-of-fragment feature | **out of scope** — filtered, with a reason |

There is deliberately **no "model bug" bucket.** That is the point of doing this
round first.

## 06 §7 — The exit criterion

Trust `desugar` enough to build RubyCore semantics against it when: round-trip
agreement on the filtered bootstraptest corpus is total and the `expected`
cross-check passes; rule coverage is saturated, every rule and every reachable
rule-pair exercised; prong-2 fuzzing sits at a stable disagreement rate trending
to zero with everything triaged; the prong-3 obligation list passes under `obs⁺`;
and the pure checks hold across the whole corpus.

At that point a future C1 disagreement is known *not* to be a front-end artifact —
which is the property the whole ordering was for.

## 06 §8 — Open

- **[?]** How faithful must `render_core` be to keep the trusted base small? Could
  it be skipped by emitting an AST that Prism itself can unparse, reusing a
  maintained unparser?
- **[?]** Which AST reductions preserve parseability *and* trace-observability
  well enough to hand to a general structure-aware reducer?
- **[?]** Does scope-aware generation bias away from the very
  `NameError`/`NoMethodError` paths that exercise `method_missing`-relevant
  desugarings? May need a deliberate undefined-reference mode.

---
