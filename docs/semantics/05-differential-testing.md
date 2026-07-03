# RubyCore Semantics — 5: Differential-Testing Methodology

> Notation: `00-notation-and-syntax.md`. This artifact expands and supersedes the sketch
> in `../../PROJECT_PLAN.md` §6. It defines *how we establish and keep confidence that
> the Lean model agrees with real Ruby*, and how that testing effort transfers to the
> inductive relation (not just the executable interpreter).

---

## 1. Goal and the two testable claims

Differential testing must establish two distinct claims, against two different oracles:

- **C1 — Model accuracy.** For every program in the modeled fragment, the Lean
  interpreter's observation equals CRuby's. *Oracle: pinned CRuby.*
- **C2 — Desugaring soundness.** For every surface program, `desugar(P)` and `P` have
  the same observation *under CRuby*. *Oracle: CRuby alone — the Lean model is not
  involved.* This isolates front-end bugs from semantics bugs.

Both feed a third, non-testable claim discharged by proof: **C3 — Adequacy**
(interpreter ⟺ inductive relation, PROJECT_PLAN §7). C3 is the bridge that turns
test-grade evidence about the interpreter into proof-grade evidence about the relation.
The sequencing rule (from the JSCert playbook): **make C3 a Phase-2 gate** — until it
holds, all testing pins only the executable, and confidence does not transfer to the
definition of record.

---

## 2. Prior art we are copying, deliberately

| Source | What we take |
|--------|--------------|
| **KJS** (Park, Ştefănescu, Roșu, PLDI'15) | *Semantic-rule coverage* as the headline metric (§6); the finding that a conformance suite under-covers rules, and closing the gap finds real bugs. |
| **JSCert / JSRef** (Bodin et al., POPL'14; Sampaio et al.) | Dual relation+interpreter, interpreter *proven* against the relation, then validated on a conformance suite; disagreements reveal bugs in spec, tests, *and* implementations. |
| **Csmith** ("Finding and Understanding Bugs in C Compilers", Yang, Chen, Eide & Regehr, PLDI'11) | *Randomized differential testing* with **majority voting** across ≥3 implementations (no oracle) — found >325 GCC/LLVM bugs. Its hard-won lesson: the central problem is **generating valid programs** (free of undefined/unspecified behavior), and **test-case reduction is mandatory infrastructure** — naïve C reducers reintroduce UB and yield "small but useless" programs. Our RubyCore-AST generation + semantics-aware shrinking (§4.1, §5) are the direct response. |
| **Superion** ("Grammar-Aware Greybox Fuzzing", Wang, Chen, Wei & Liu, ICSE'19) | **AST-level, coverage-guided** mutation: parse inputs to trees, splice subtrees, trim by subtree so mutants stay grammar-valid (100% validity vs AFL's 74–89%). It carries fuzzing *past the parser* into execution — our model for structure-aware generation (§4.1). Caveat we must fill: Superion has **no correctness oracle** (finds only crashes/memory-safety bugs); differential testing supplies the "wrong-but-non-crashing" oracle it lacks. |
| **EMI** (Le et al., PLDI'14) | *Metamorphic* testing via behavior-preserving mutation — no oracle needed. We get this for free from our desugarings (§4, claim C2). |
| **Redex** (Klein et al., "Run Your Research", POPL'12) | Property-based generation *directly from the semantics definition*. |

The Ruby-specific corpora are two large, ready-made suites: **`ruby/spec`** (executable,
mspec-based) and **MRI's `test/`** suite. And there is a **direct Ruby precedent for this
methodology**: *The Essence of Ruby* (Ueno et al., APLAS 2014) already differentially
tested an SML reference interpreter against the CRuby 1.9.3 test suite — but only on a
narrow, hand-selected slice (26/28 block-and-jump cases). Our contribution over that
baseline is *scale and automation*: generation, minimization, three-way triangulation,
and semantic-rule coverage, against a *mechanized* Lean semantics rather than an
unverified SML interpreter (see PROJECT_PLAN §3).

---

## 3. The oracle harness and the observation function

```
     RubyCore AST (generated or ingested)
        │  pretty-print
        ▼
   Ruby source ──┬───────────────▶  CRuby (pinned, containerized, deterministic)
                 │                        │  harness prelude → obs_ruby (JSON)
                 └──▶ Lean interpreter ───┤
                          run(fuel, ·)    │  final Config → obs_lean (JSON)
                                          ▼
                              normalize + compare (§3.2)
                                          │
                          AGREE ──────────┴────────── DISAGREE → §5 pipeline
```

### 3.1 What we observe (`obs`)

Per PROJECT_PLAN §6.1, `obs = (stdout-trace, result-repr, exc-repr, heap-proj)`. Concretely
the CRuby side is produced by a **harness prelude** wrapped around the program:

```ruby
# harness.rb (conceptual)
$stdout.sync = true
result = begin
  __PROGRAM__                          # the program under test, as the last expression
rescue Exception => e                  # capture EVERYTHING incl. non-StandardError
  __exc = e
end
emit_json(
  stdout:  captured_stdout,
  result:  __exc ? nil : safe_inspect(result),
  exc:     __exc && [__exc.class.name, __exc.message],
  heap:    heap_projection(__roots)    # canonical ivar dump over reachable objects
)
```

The Lean side computes the identical projection from the final `Config`. Equality of the
two JSON blobs (after §3.2 normalization) is *observational equality*.

### 3.2 Determinism and normalization — the hard part

Legal-but-nondeterministic outputs must be quotiented out on **both** sides, or every
run is a false positive:

| Source of nondeterminism | Neutralization |
|--------------------------|----------------|
| `object_id` / `#inspect` addresses (`#<Foo:0x…>`) | run in allocation order; rewrite ids to allocation-index integers on both sides |
| `Hash`/`Set` iteration seed | fix `RUBY_HASH_SEED=0` (or `--disable-frozen-string-literal` parity); model uses insertion order (artifact 01 §3) |
| `Time.now`, `rand`, `SecureRandom` | stub to fixed values in the prelude; model has no clock/RNG (artifact 00 §6 excludes them) |
| backtrace line numbers / file paths | drop from `exc-repr`; keep only class + message |
| GC-observable effects, `ObjectSpace` | out of scope (PROJECT_PLAN §4); reject programs that touch them |
| floating-point formatting | compare `Float` by canonical decimal + bit-pattern, not string |

Pin **one** CRuby patch level in a container image (`ruby:X.Y.Z-slim`). Semantics drift
across minors is real (kwargs 2.7→3.0, `Hash` methods, `Integer#/` rounding). The model
targets that exact version; testing against a *second* version is a separate experiment
(§7).

---

## 4. Test-case sources (four, by what each is good at)

1. **Handwritten per-rule oracles.** One (or a few) per inference rule across artifacts
   00–04. Purpose: seed rule coverage (§6), serve as regression tests, and double as
   executable documentation. Naming convention ties each to its rule, e.g.
   `t/dispatch/SUPER_through_prepend.rb`.

2. **Self-contained corpora — the three-pronged approach** (detailed for the front end in
   artifact 06 §4): (i) **MRI `bootstraptest/`** — curated, core-focused, genuinely
   self-contained program strings that also ship an oracle value; (ii) **Superion-style
   grammar-aware fuzzing** seeded from (i); (iii) **AI-agent targeted examples** for the
   semantic corners. Note we deliberately **do not** use `ruby/spec` (mspec) or MRI
   `test/` (minitest) as-is: those are *unit-test-framework* suites — the framework is not
   part of the language, and example bodies are coupled to `describe`/`before`/`let`
   setup, so they aren't self-contained. Harvesting them is deferred. A program that uses
   an unmodeled feature is *skipped with a reason*, never silently (PROJECT_PLAN "no silent
   caps").

3. **Grammar-based generation over RubyCore** (§4.1) — the bulk of adversarial coverage
   (this is prong (ii) above, generalized past the front end to the full semantics).

4. **Rails vertical-slice scenarios** — later-phase payoff; trimmed but real Rails idioms
   run end-to-end through both engines (artifact 10, forthcoming).

### 4.1 Generation, adapted to Ruby's dynamism

You cannot generate "well-typed" Ruby the way Csmith generates valid C — Ruby has no
static validity filter. So we invert the Csmith move:

```
  generate RubyCore AST from the grammar (artifact 00 §4, weighted toward modeled forms)
      │  pretty-print to surface Ruby
      ▼
  run under CRuby as a FILTER:
      · parse/load error            → discard (not a meaningful program)
      · times out / non-terminating → discard (or keep as a divergence test, §7)
      · terminates (value OR raise)  → KEEP; its CRuby observation IS the oracle
      ▼
  feed kept programs to the differential comparator (§3)
```

CRuby itself defines "meaningful," not a type system. Generation is **weighted** toward
the object-model/dispatch core (artifact 02) because that is where 80% of the value sits
(PROJECT_PLAN §2), and biased to reuse a small pool of names so that dispatch, `super`,
and `method_missing` paths actually fire instead of degenerating into `NoMethodError`.

### 4.2 Metamorphic testing — oracle-free, from our desugarings (the EMI lever)

Because we own the desugaring functions (artifact 00 §5), each is a behavior-preserving
transform we can check *with no model involvement*:

- **Desugaring soundness (claim C2):** `obs_ruby(P) == obs_ruby(desugar(P))` for surface
  `P`. Validates the front-end independently of the semantics.
- **Refactoring relations:** `attr_accessor :x` ≡ explicit getter/setter pair;
  `a && b` ≡ `if a then b else a`; `unless c` ≡ `if !c`; `x ||= e` ≡ `x || (x = e)`.
  Any divergence is a bug regardless of oracle, and cheaply generated at scale.

---

## 5. Disagreement pipeline: minimize, then triage

Every disagreement runs this pipeline before a human (or agent) looks at it:

```
  disagreement
     │
     ▼  delta-debug the RubyCore AST: repeatedly delete/replace subtrees with `nil`
        while the disagreement persists  →  minimal reproducer
        (structure-aware reducer, e.g. shrinkray [DRMacIver] driven by a
         "disagreement still reproduces?" predicate; see §7 on shrink soundness)
     │
     ▼  three-way triangulation: also run under a SECOND implementation
        (TruffleRuby or JRuby)
     │
     ├─ CRuby & TruffleRuby agree, we differ      → MODEL bug (fix a rule)
     ├─ desugar(P) already differs under CRuby     → DESUGAR bug (claim C2 failure)
     ├─ all three implementations differ           → UNDER-SPECIFIED → mark [?], do not "fix"
     ├─ difference is only in a normalized field    → OBSERVATION bug (fix §3.2 normalizer)
     └─ program uses an unmodeled feature           → OUT OF SCOPE → document, skip with reason
```

The shape of the disagreement tells you *where* the defect lives — this is exactly how
JSCert found bugs in browsers and in test262 rather than assuming its own model was
always wrong.

---

## 6. Metrics — making "accurate, explainable, useful" measurable

- **Agreement rate** per corpus. Target: 100% on the modeled fragment; every miss is a
  filed defect in one of the §5 buckets.
- **Fragment coverage:** % of `ruby/spec` / MRI examples that are in-scope *and* pass.
- **Semantic-rule coverage (the KJS metric):** instrument the interpreter to emit the
  set of relation rules fired per run; aggregate over the corpus. An untouched rule is
  either dead (model bug) or under-tested (write a targeted program — where KJS found
  real engine bugs). This *is* the explainability deliverable: every passing behavior
  ships with its derivation (the ordered list of rules that produced its `obs`).
- **Fuzzer disagreement rate over time:** should trend to zero as the model matures; a
  rising rate flags a newly-modeled feature with bugs.
- **Reduction quality:** median size of minimized reproducers (smaller = healthier
  triage loop).

---

## 7. Extensions and open questions

- **[?] Divergence testing.** Non-terminating generated programs are discarded today.
  Better: run CRuby with a wall-clock cap and the model with a fuel cap, and check they
  *both* fail to produce a value (co-divergence) — distinguishing "diverges" from
  "model ran out of fuel too early" (PROJECT_PLAN §7's fuel-vs-relation subtlety).
- **[?] Cross-version prediction.** Given the model pinned at version X, can it *predict*
  the behavioral diff to version Y? A strong signal the model captures real semantics.
- **[?] Coverage-guided generation.** Feed rule-coverage back into the generator (à la
  AFL) to steer toward untouched rules, instead of uniform grammar sampling.
- **[?] Property-based invariants.** Beyond `obs` equality: check metatheoretic
  invariants on every run (determinism, the unwind-soundness invariant of artifact 04
  §6, heap well-formedness) as cheap always-on assertions.
- **[?] Shrinking soundness.** Delta-debugging must preserve *parseability*; shrinking a
  RubyCore AST is safer than shrinking source text, but splat/block-arg edits can change
  arity semantics — the reducer needs semantics-aware moves. A general structure-aware
  reducer such as **shrinkray** (DRMacIver) can drive this given a predicate that re-runs
  the differential comparison; the open question is which AST-level moves are
  behavior-safe enough to expose to it.
