# Prong 2 — Grammar-Aware Fuzzing: Design Note & Feasibility

> Status: **design/feasibility only — not yet implemented.** This is the plan for the
> second corpus prong of the desugar differential-testing harness (artifact 06 §4,
> prong 2). Prong 1 (bootstraptest) and the hand-written adversarial seeds (prong 3 seed)
> already run; see [`README.md`](README.md).
>
> References: [`README.md`](README.md) §The method (the desugar-first
> method), `../difftest/README.md` §Methodology (artifact 05 §4, generation), and the
> papers in `../../ruby_papers/` — Csmith (PLDI'11) and Superion (ICSE'19).

## 0. Goal

Automatically generate a high volume of **parseable, deterministic** surface-Ruby
programs that exercise the `desugar` rewrite rules — and especially their *combinations* —
to drive up desugaring-rule (and rule-pair) coverage beyond what the curated corpora
reach. Feed them through the existing round-trip oracle (`Roundtrip.check`).

## 1. Feasibility summary

Prong 2 is **quick to set up** — a few hours of self-contained Ruby with zero new
dependencies and zero harness changes. Two structural advantages plus one big
non-problem:

- **Integration cost ≈ zero.** `bin/run` already globs any `.rb` under `corpus/`, and
  `Roundtrip.check(src)` takes a source string. A generator is "wired in" the moment it
  can emit strings — write to `corpus/generated/` or pipe straight into `Roundtrip.check`.
- **The hard part of Csmith does not apply to us.** Csmith's entire difficulty was
  generating C free of the 191 undefined + 52 unspecified behaviors, because in C an
  invalid program yields a meaningless differential result. For desugar testing, a
  **deterministic error is a valid oracle case** (artifact 06 §3) — `desugar` must
  preserve a `NoMethodError` as faithfully as a value. So we only need programs that are
  **parseable + deterministic**, not "valid," and we can skip Csmith's static-analysis
  machinery entirely.
- **The residual hazards are cheap** (non-termination, nondeterminism) — see §4.

## 2. Design space

| Approach | Quick? | Notes |
|----------|--------|-------|
| **A. Generate a surface AST, render to Ruby text** | ✅ yes | We own the node set and renderer, so output always parses and stays in/near the fragment. Reuses the exact `parse → desugar → render_core → CRuby` pipeline. **Recommended.** |
| **B. Superion-style mutation (splice seed subtrees)** | ❌ not yet | Requires rendering a *mutated Prism AST* back to source, but **Prism has no unparser**, and `render_core` handles only RubyCore (post-desugar), not arbitrary surface Prism nodes. Becomes cheap once Option A exists — splice the surface AST we already render. |
| **C. Off-the-shelf grammar fuzzer (grammarinator/ANTLR, as Superion uses)** | ⚠️ heavier | Adds a Python+ANTLR toolchain and an approximate Ruby grammar that generates mostly out-of-fragment code. More setup, less targeted than A. |

**Decision: start with A.** It is the fastest path to value and makes B nearly free later
(mutation = splicing the same surface AST we can already render).

## 3. Recommended design (Option A)

A small **surface generator** emitting a tagged *surface* AST — like RubyCore, but with
the **sugar heads** that trigger rewrites (`:unless`, `:until`, `:and`, `:or`,
`:opassign`, `:interp`, plus the shared literal/`send`/`if`/`while`/`def`/`seq` forms) —
paired with a **surface renderer** (the generator's twin, roughly the size of
`lib/render.rb`). Everything downstream is reused:

```
  gen surface-AST ─surface_render─▶ Ruby text ─▶ [existing pipeline]
                                                    Prism.parse → desugar → render_core
                                                    → obs⁺(text) ≟ obs⁺(render_core(desugar(text)))
```

The generated text goes through the identical path as a corpus file, so the generator's
only genuinely new code is (i) the random surface-AST builder and (ii) its renderer.

Three design choices matter more than the generator plumbing:

1. **Scope-awareness — defeats the real enemy, shallowness.** Maintain an environment
   during top-down generation: only reference locals already bound and methods already
   `def`'d, drawn from a small name pool so dispatch/`super`/interpolation paths actually
   fire instead of every program dying at line 1 with `NameError` (artifact 06 §4.2).
   This is the single highest-leverage feature and only modestly more code. A naive
   generator without it produces valid-but-shallow programs that never reach nested sugar.
2. **Weight productions toward the sugar**, and track generated forms so we can bias
   toward untouched rules and, more importantly, untested **rule pairs** (interpolation
   inside a `while` inside an `&&`). Rule-pair interactions are where desugar bugs cluster
   (artifact 06 §5) and where prong 2 earns its keep over the hand-written seeds.
3. **Fragment-restricted vocabulary** so few programs are wasted as out-of-fragment,
   keeping oracle throughput useful.

## 4. Risks and cheap mitigations

| Risk | Mitigation |
|------|------------|
| **Non-termination** (generated `while` / recursion) | Emit loops only in a bounded counter form; do not generate self-recursive calls; rely on the existing `Observe` timeout as a backstop. |
| **Nondeterminism** | The fragment vocabulary has no `Time`/`rand`/threads by construction → generated programs are deterministic for free. Seed the generator PRNG (`Random.new(seed)`) for reproducible corpora. |
| **Object-identity in output** | Already handled by the `obs` address normalizer (implementation-choices.md C6). |
| **Out-of-fragment waste** | Controlled by the restricted vocabulary; a low skip rate falls out. |
| **Oracle throughput** | ~2 CRuby spawns per program (~100 ms) ⇒ thousands/hour single-threaded — fine for a first version; parallelize later if needed. |

## 5. Effort and value

- **v0 (naive, no scope-awareness):** ~100 lines, ~1 hour. Valid but shallow; useful only
  for smoke-testing `render_core`/`desugar` robustness on odd nestings.
- **v1 (scope-aware, sugar-weighted, surface-AST + renderer):** ~250–350 lines, a few
  hours. The real target — drives rule-pair coverage, reuses the whole pipeline.
- **Later:** mutation (Option B) is a small add once the surface AST exists; coverage-
  guided steering (feed `Desugar::RULES` gaps back into generation weights, à la AFL) is a
  natural v2 (artifact 05 §7).

**Value ceiling (be honest):** prong 2 excels at breadth and rule *combinations*, and will
shake out `render_core`/`desugar` crashes on valid-but-weird trees. But because `desugar`
is mostly structural, the subtle *semantic* obligations (once-only evaluation, ordering)
are better hit by the trace-augmented adversarial seeds (prong 3). Prong 2 **complements**
prong 3, not replaces it, and it cannot find "wrong-but-non-crashing" behavior beyond what
the round-trip oracle already checks.

## 6. Suggested build order (when we implement)

1. Define the surface-AST node set (RubyCore heads + sugar heads) and `surface_render`.
2. Naive random builder (v0) → confirm generated programs flow through `Roundtrip.check`
   and mostly land in-fragment.
3. Add scope-awareness + sugar weighting (v1) → measure rule / rule-pair coverage lift
   over the seeds + bootstraptest baseline.
4. Wire coverage feedback and (optionally) surface-AST mutation (Option B).

## 7. Open questions

- **[?]** Should the surface generator share a node vocabulary with a future prong-3
  agent (so both target the same fragment), or stay independent?
- **[?]** How to bound loops without biasing away from interesting `while` interactions —
  counter form vs. a generation-time "fuel" annotation stripped before rendering.
- **[?]** Do we generate deliberate `NameError`/`NoMethodError` shapes (to exercise
  `method_missing`-relevant desugarings) as a separate mode, given scope-awareness
  otherwise avoids them (artifact 06 §8)?
