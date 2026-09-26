# Testing methodology (artifact 05)

How confidence that the Lean model agrees with real Ruby is established and kept,
and how that effort transfers to the inductive relation rather than only to the
interpreter. Code comments cite this section as *"artifact 05 §N"*; the numbering
below is that addressing and is kept stable.

## 05 §1 — The two testable claims, and the one that is proved

- **C1 — model accuracy.** For every program in the modeled fragment, the Lean
  interpreter's observation equals CRuby's. *Oracle: pinned CRuby.*
- **C2 — desugaring soundness.** For every surface program, `desugar(P)` and `P`
  have the same observation *under CRuby*. *Oracle: CRuby alone — the Lean model
  is not involved.* This isolates front-end bugs from semantics bugs, and is what
  `desugar/` exists to run (see [the round-trip method](../front-end/method.md)).
- **C3 — adequacy.** Interpreter ⟺ inductive relation. Not testable; discharged by
  proof (`ruby-lean/RubyCore/Proof/Adequacy.lean`). C3 is the bridge that turns
  test-grade evidence about the interpreter into proof-grade evidence about the
  definition of record. Until it holds, testing pins only the executable.

## 05 §2 — Prior art this deliberately copies

| Source | What is taken |
|---|---|
| **KJS** (Park et al., PLDI'15) | *semantic-rule coverage* as the headline metric (§6) — a conformance suite under-covers rules, and closing the gap finds real bugs |
| **JSCert/JSRef** (Bodin et al., POPL'14) | relation + interpreter, the interpreter proved against the relation, then validated on a suite; disagreements reveal bugs in the spec and the tests, not only the model |
| **Csmith** (Yang et al., PLDI'11) | randomized differential testing; and its hard-won lesson that **test-case reduction is mandatory infrastructure**, not a nicety |
| **Superion** (Wang et al., ICSE'19) | AST-level, coverage-guided mutation — splice and trim by subtree so mutants stay grammar-valid. It has *no* correctness oracle; differential testing supplies the one it lacks |
| **EMI** (Le et al., PLDI'14) | *metamorphic* testing via behavior-preserving mutation — which the desugarings give for free (§4) |

There is a direct Ruby precedent: *The Essence of Ruby* (Ueno et al., APLAS'14)
differentially tested an SML interpreter against CRuby 1.9.3 — but on a
hand-picked slice of 28 block-and-jump cases. The contribution over that baseline
is scale and automation: generation, minimization, and rule coverage, against a
*mechanized* semantics.

## 05 §3 — The observation, and normalization

`obs = (stdout-trace, result-repr, exc-repr)` — see [What is compared](engine.md#what-is-compared-observation) for
what the engine actually implements. Legal-but-nondeterministic outputs must be
quotiented out on **both** sides or every run is a false positive:

| Source of nondeterminism | Neutralization |
|---|---|
| `object_id` / `#inspect` addresses (`#<Foo:0x…>`) | rewrite to allocation-order indices on both sides |
| `Hash`/`Set` iteration seed | pin `RUBY_HASH_SEED=0`; the model uses insertion order |
| `Time.now`, `rand`, `SecureRandom` | out of fragment; programs touching them are excluded |
| backtrace line numbers and file paths | dropped — `exc-repr` keeps class + message only |
| GC-observable effects, `ObjectSpace` | out of scope; such programs are rejected |
| float formatting | compare canonically, not as strings |

One CRuby version is pinned. Semantics drift across minors is real (kwargs
2.7→3.0, `Integer#/` rounding); testing against a *second* version is a separate
experiment (§7).

## 05 §4 — Where test programs come from

1. **Handwritten per-rule oracles** — one or a few per inference rule across
   artifacts 00–04. Seeds rule coverage, serves as regression tests, doubles as
   executable documentation.
2. **Self-contained corpora** — MRI's `bootstraptest` (tier 0). Note what is
   *not* used: `ruby/spec` (mspec) and MRI `test/` (minitest) are
   unit-test-*framework* suites; the framework is not part of the language and
   example bodies are coupled to `describe`/`before`/`let` setup, so they are not
   self-contained. Harvesting them is deferred.
3. **Grammar-based generation over the AST** (tier 1) — the bulk of adversarial
   coverage.
4. **Adversarial generation** (tier 3) — for the semantic corners random
   generation is unlikely to hit.

**Generation, adapted to Ruby's dynamism.** You cannot generate "well-typed" Ruby
the way Csmith generates valid C — Ruby has no static validity filter. So the
Csmith move is inverted: generate from the grammar, render to source, then run
under **CRuby as a filter** — parse error or timeout ⇒ discard; terminates with a
value *or* a raise ⇒ keep, and its CRuby observation *is* the oracle. CRuby
defines "meaningful", not a type system. Generation is weighted toward the
object-model and dispatch core, and biased to reuse a small pool of names so that
dispatch, `super` and `method_missing` paths actually fire instead of degenerating
into `NoMethodError`.

**The metamorphic lever (EMI, oracle-free).** Because the desugarings are ours,
each is a behavior-preserving transform checkable with no model involvement: C2
itself, plus refactoring relations (`attr_accessor :x` ≡ the getter/setter pair;
`a && b` ≡ `if a then b else a`; `x ||= e` ≡ `x || (x = e)`). Any divergence is a
bug regardless of oracle, and these are cheap to generate at scale.

## 05 §5 — Disagreement triage

Every disagreement runs this before anyone looks at it: delta-debug the AST —
repeatedly delete or `nil` out subtrees while the disagreement persists — to a
minimal reproducer, then read *the shape* of the disagreement to locate the
defect:

| Shape | Verdict |
|---|---|
| a second implementation agrees with CRuby, we differ | **model** bug — fix a rule |
| `desugar(P)` already differs under CRuby | **desugar** bug — a C2 failure |
| all implementations differ | **under-specified** — mark `[?]`, do not "fix" |
| difference is confined to a normalized field | **observation** bug — fix the normalizer |
| the program uses an unmodeled feature | **out of scope** — skip with a reason |

That last row is a standing norm: **no silent caps.** A program is never dropped
without a recorded reason.

## 05 §6 — Metrics

- **Agreement rate** per corpus — 100% on the modeled fragment; every miss is a
  filed defect in one of the §5 buckets.
- **Fragment coverage** — what fraction of a corpus is in scope at all.
- **Semantic-rule coverage** (the KJS metric) — the set of rules fired per run,
  aggregated. An untouched rule is either dead (model bug) or under-tested. This
  *is* the explainability deliverable: a passing behavior ships with the ordered
  list of rules that produced its `obs`. **Designed, not yet built** — named in the
  paper as the right next evaluation.
- **Disagreement rate over time** — should trend to zero; a rise flags a
  newly-modeled feature with bugs.
- **Reduction quality** — median size of minimized reproducers.

## 05 §7 — Open

- **[?] Divergence testing.** Non-terminating generated programs are discarded
  today. Better: cap CRuby by wall clock and the model by fuel and check they
  *both* fail to produce a value — distinguishing "diverges" from "ran out of fuel
  too early".
- **[?] Cross-version prediction.** Can a model pinned at version X predict the
  behavioral diff to version Y? A strong signal that it captures real semantics.
- **[?] Coverage-guided generation.** Feed rule coverage back into the generator
  to steer toward untouched rules, rather than sampling the grammar uniformly.
- **[?] Property-based invariants.** Beyond `obs` equality: check determinism, the
  unwind-soundness invariant (artifact 04 §6) and heap well-formedness as cheap
  always-on assertions.
- **[?] Shrinking soundness.** Shrinking an AST is safer than shrinking source
  text, but splat and block-arg edits can change arity semantics; which AST moves
  are behavior-safe enough to hand to a general reducer is open.
