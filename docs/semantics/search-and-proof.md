# Search and proof — how Direction A and Direction B come together

**Status: brainstorm / design notes. Nothing here is built** (except where marked
*measured*, which records results from the existing engine). Companion to
[`concolic-dataflow.md`](concolic-dataflow.md) (how the model emits dataflow) and
[`../../../type-safety-by-reachability.md`](../../../type-safety-by-reachability.md)
(the two directions themselves).

Origin: a 2026-08-03 design conversation, prompted by *"what would it take to reason
about arrays and hashes with z3's theory of arrays?"* — which turned into a much
broader discussion about where on the concrete↔symbolic spectrum this checker should
sit, and ended somewhere more interesting: **the two directions are not independent
products; each supplies what the other lacks.**

---

## 1. The spectrum, and where we sit

| | Strategy | State per step | Aliasing / dispatch |
|---|---|---|---|
| concrete | fuzzing (Phase 1, `Search/Random.lean`) | one concrete state | concrete |
| **concolic** | **one concrete path + path condition (Phase 2, `concolic/`)** | **one concrete state + shadow terms** | **concrete** |
| merged | state-merging symbolic execution (*veritesting*) | symbolic within a region | partly symbolic |
| symbolic | full symbolic execution / BMC | symbolic | symbolic |
| relational | narrowing over an inductive `Step` (D4) | symbolic | symbolic |

We are deliberately at row 2. The reason is not conservatism — it is that
**concreteness buys three specific things that Ruby makes expensive to give up**:

1. **Aliasing is concrete.** Ruby collections are mutable heap objects with reference
   identity — the thing theory-of-arrays models worst. On a concrete run every
   reachable `ObjId` is *known*, so `a = b; b << 3` needs no symbolic pointer
   reasoning. Symbolic-start loses this.
2. **Dispatch is concrete.** Method tables are settled by concrete boot, so
   `recv.m` resolves against a real heap. Symbolic-start makes the *method tables*
   symbolic — the path explosion the whole design exists to avoid.
3. **The self-check oracle exists.** Every emitted term is validated against the
   machine's actual value (`concolic-dataflow.md` §6.4). That is why a mirroring bug
   costs *precision* rather than *soundness* — and it was measured to work
   (deliberately mis-mapping `*` to addition produced `SELF-CHECK FAILED`, term
   dropped). **Pure symbolic execution has no concrete run to check against**; the
   safety net simply is not available.

Any move rightward on this table must price in all three.

## 2. D5 — finite-domain exhaustive splitting (Rosette's mechanism, adapted)

### 2.1 What Rosette actually guarantees

Read from the paper (see §7): Rosette supports **only** booleans and finite-precision
integers as primitive symbolic constants; everything else is a **symbolic union** —
a set of guarded values arising from `if` merges, whose guards are disjoint. `for/all`
disassembles a union, applies unlifted code per component, and reassembles.

The invariant that matters (Rosette §3.4): symbolic execution is *sound and complete*
— the symbolic state encodes **"only and all"** concrete states reachable by some
concrete execution. `for/all` is **precision-preserving** because it splits an
*already exhaustive* union: exhaustive-in, exhaustive-out.

**Correction recorded:** an earlier note in this project equated our `opaque` with
symbolic reflection. That is wrong. Reflection replaces "cannot handle symbolically"
with a *finite, exhaustive, guarded case split over concrete possibilities* — keeping
the full relationship. `opaque` **discards** the term. Reflection is
precision-preserving; `opaque` is precision-losing.

### 2.2 The proposal, and its one divergence

The idea: keep symbolic terms over atomic values only; when execution hits something
unmodeled, execute **concretely by cases**; re-enter the symbolic world at the output.
For infinite domains, obtain the cases by lightweight sampling (n≈5).

Sampling is where this diverges from Rosette: a sampled union is **"only" but not
"all"** — each case is a real execution, but the guards do not cover the space. That
is an **under-approximation**.

**Which is acceptable for us, with one hard rule.** Direction A replays and confirms
every witness, so an under-approximation cannot produce a false positive — only
missed witnesses, which is incompleteness we already have. But it must **never** feed
a safety claim. Verdicts already say "NOT a proof of type-safety"; sampled unions
would make that non-negotiable.

### 2.3 The better version: our domains are already finite

**Concrete boot hands us finite domains for exactly the interesting cases:**

- array indices — bounded by the concrete length
- hash keys — bounded by the concrete key set
- class tags — bounded by the booted class table
- symbols — finite, drawn from the program text
- booleans

For these, **enumerate exhaustively** and Rosette's "only and all" property is
recovered exactly — no sampling, no asterisk. Sampling is then reserved for genuinely
infinite domains where the guard is inexpressible (which strings? which floats?), and
labelled as an under-approximation on the frontier.

Strategically: **the ai4r nil-bug case is in the finite category.** `@q[state]` where
`state` comes from `states[i]` has domain `{states[0], states[1], states[2], nil}`.
So exhaustive case-splitting may handle it **without theory of arrays at all** —
which would retire most of the A→C refactor sketched in `concolic-dataflow.md` §8.2.

### 2.4 Architectural fit: cases as goals, not forks

Rosette forks and merges *inside* one symbolic evaluation. We run one concrete path
with a shadow, so mid-run forking is a large change. The natural fit instead:

> **make each case a directed goal, not a fork** — queue an input that forces case *k*
> and let the concolic loop explore it as a separate concrete run.

Consequences: no machine forking, no merge function, every run fully concrete and
self-validating, and it **reuses the `DispatchRisk` machinery already built** (which
is literally a one-case instance of this).

This also dissolves the stated hard part. "Faithful samples of each branch" is a
problem only if you *sample*; if the case split is a **solver goal**, the solver
produces an input that provably takes case *k* under the path condition, and we then
run it. **Faithfulness is by construction.**

Costs: path explosion (N cases → N runs, multiplying along a path — Rosette exposes
`for/all` for exactly this tuning reason), and data-dependent case counts (a
3-element array is fine; a 10k-entry hash is not). Mitigations: split **lazily** —
only when the value feeds a branch or a dispatch — and cap the split width, reporting
the cap as a bound.

## 3. Input-bounded loops — *measured*, and it reframes the problem

Test case (committed as `concolic/programs/loop_sum.rb` and `array_fold_sum.rb`):
`sum(1..N)` with a downstream condition `sum == 15`, written two ways — an explicit
`while` loop, and building an array then folding.

**Finding 1 — no infinite-execution problem.** The loop's own conditions are
recorded, which *pins the trip count*:

```
N=3 ⟹  1≤n ✓,  2≤n ✓,  3≤n ✓,  ¬(4≤n)      ⟹ path condition forces n = 3
```

So "infinitely many ints to execute on" becomes "one path per trip count", explored
lazily. Generational search then walks exactly the triangular numbers and finds N=5:

```
inputs=[0]→0  [1]→1  [2]→3  [3]→6  [4]→10  [5]→typestuck NoMethodError
```

**Finding 2 — the symbolic content moves to the path condition.** *Within* a path the
result is a **constant**, not a symbol: at N=3, `sum` folded to `lit 6` and
`sum == 15` folded to `lit 0`. Correct, but unflippable. There is nothing to
"re-enter the symbolic world" with — the symbolism relocated into the path condition.

**Finding 3 (the surprise) — collection opacity cost nothing here.** The array+fold
version behaves *identically* despite `sum` being fully `opaque` (the `iterK`
iterator and collection contents are untracked), because the enumeration is driven by
the `while`-loop conditions and the bug is found by **execution**, not by solving the
`sum` constraint. Evidence that collection-term tracking matters less than expected
when loops are input-bounded — an argument against rushing into theory-of-arrays.

**Finding 4 — the real weakness is linearity, not infinity.** Reaching `sum > 10⁶`
needs ~1414 unrollings; and an *unsatisfiable* target (`sum == 1000000`, not a
triangular number) searches forever without ever proving unreachability.

**Cheap fix available:** *exponential trip-count probing*. Instead of flipping the
loop-exit to `n ≥ k+1`, ask for `n ≥ k+Δ` with Δ doubling — turning linear-in-N into
logarithmic-in-N for reachable targets. ~20 lines in the search loop, no new theory.
Does not help unsatisfiable targets.

## 4. Guiding search by "closeness" (branch distance)

The idea: quantify how close a condition is to holding (`|sum − 15|`), and use an
estimate of `d(sum)/dn` to decide which way to push inputs.

**This is well-trodden** — see §7 for citations. `|sum − 15|` is textbook *branch
distance* (Korel 1990), paired with the alternating-variable method; it grew into
search-based software testing. The gradient version is essentially **Angora**
(byte-level taint + *numerical* gradient descent on branch distance) and **NEUZZ**
(learn a smooth neural surrogate, descend on that).

**But note why those systems estimate gradients numerically or learn them: they have
no model of the program.** That is a workaround for missing semantics.

### 4.1 The part that is genuinely underexplored

We have a formal semantics, so we need not estimate the landscape. And we can go
beyond derivatives: the concolic runs *already emit an exact integer sequence*.

```
sum(0)=0, sum(1)=1, sum(2)=3, sum(3)=6, sum(4)=10
Δ  = 1,2,3,4 ;  Δ² = 1,1,1  (constant ⟹ degree 2)  ⟹  sum = n(n+1)/2
```

Then **solve analytically** instead of descending:

- `sum == 15` → `n = 5`, jump straight there;
- `sum == 1000000` → no integer root → **provably unreachable**, which no amount of
  probing or gradient descent can ever establish.

That asymmetry is the point: distance-guided search can only say *"not found yet"*; a
recovered closed form can say **UNSAT**.

### 4.2 Known pitfalls of the distance metric

- **Plateaus.** `if h(x) == 12345` for a hash `h` — the landscape is flat, distance
  carries no information. (Our `narrowNeedle` is fine: a direct comparison.)
- **Discreteness.** Trip counts are integers, so it is finite differences, not
  derivatives — *better* for us (exact), but it breaks the continuous framing.
- **Local minima / multiple inputs** — the classic search-based-testing failure mode.
- **Non-numeric conditions** need their own distance (edit distance for strings;
  what laf-intel/Steelix approximate by splitting multi-byte comparisons).

Assessment: the distance/gradient half is the weaker and better-trodden one. **Summary
inference, validated as an invariant, is the strong half** — better suited to what we
have (a semantics, a proof framework, already-collected samples) and it attacks the
one weakness we *measured* (§3, Finding 4).

## 5. Getting summaries: from samples, and from the code

### 5.1 From samples

1. **Finite differences (Newton forward-difference).** Exact, deterministic, ~20
   lines, no dependencies; covers most real loop accumulators. **Start here.**
2. **Linear recurrence guessing** — posit `f(n)=a₁f(n−1)+…`, solve for the `aᵢ`, close
   via characteristic roots (catches geometric/Fibonacci shapes).
3. **Ansatz + exact linear solve** over a basis `{1,n,n²,2ⁿ,…}`; accept only
   small-denominator rationals, and **validate on held-out samples**.
4. **Holonomic / D-finite fitting** — heavy artillery; almost certainly overkill.
5. **OEIS lookup** — cheeky but effective for textbook shapes (`0,1,3,6,10` →
   triangular numbers), and free to try first.

### 5.2 From the code (stronger, because we have the semantics)

6. **Induction-variable + accumulation-pattern recognition.** Classic compiler
   analysis: spot `i = i + 1` and `sum = sum + <linear in i>`, emit the recurrence
   *exactly*, close with summation identities. No guessing at the *form*; degrades
   cleanly (unrecognised shape → no summary, same discipline as `opaque`).
7. **Template + SMT.** Posit `sum = a·n² + b·n + c`; ask z3 for `a,b,c` making the
   invariant **inductive** (`Init ⇒ I`, `I ∧ body ⇒ I′`). The output is not a guess
   but an invariant *with* its inductiveness argument — exactly the shape
   `invariant_sound` consumes.
8. **Polynomial invariant generation** — Karr (affine), Rodríguez-Carbonell & Kapur /
   Müller-Olm & Seidl (polynomial, via ideals/Gröbner bases).

### 5.3 The key enabler: one *symbolic* loop iteration

To get the transition relation analytically you do **not** need full symbolic
execution — only the loop body, once, with loop-carried variables symbolic:

```
(sum, i)  →  (sum + i, i + 1)     guarded by  i ≤ n
```

That *is* the recurrence, read off the semantics rather than guessed. It is a
**bounded** symbolic execution — one iteration, no nested unbounded looping — which is
the regime the shadow already handles.

## 6. The analytic direction: CHC, and where A and B meet

"Is there *any* path to `sum == 1000000`?" is **∃-reachability over an infinite state
space**. Enumeration can never answer *no*. There are exactly two answers, with
different evidence:

- **Yes** → a witness input, certified by **execution** (Direction A, what we do);
- **No** → an **inductive invariant** `I` with `I(init)`, preservation, and
  `I ⇒ ¬bad`, certified by **proof** (Direction B).

### 6.1 We already own the checker half

`invariant_sound` *is* the "no" machinery. It is currently written against
`typeStuck`, but the proof is generic — `invariant_reaches` does the work and `safe`
is a hypothesis — so generalising it to an arbitrary bad-state predicate is a few
lines. This was always the thesis: **one checker, pluggable bad-state predicate**.
`sum == 1000000` is just a different predicate from "uncaught NoMethodError".

(For that example the invariant is `sum = i(i−1)/2`, and safety needs the
number-theoretic side condition that 10⁶ is not triangular — nonlinear integer
arithmetic, undecidable in general, routine for z3 at this size.)

### 6.2 The missing half is *discovery* — and CHC is the concrete instantiation

Encode initial state, transition relation (§5.3) and bad state as **Constrained Horn
Clauses**; hand to a CHC solver — **z3 ships Spacer**, so we already have one. It
returns either

- a **counterexample trace** → replay, certify by execution, **or**
- the **inductive invariant** → hand to `invariant_sound`, certify by proof.

Both outcomes land in machinery already built. And this is exactly the architecture
`type-safety-by-reachability.md` §4 specified — an untrusted engine *discovers* `I`, a
trusted validator *checks* it. CHC/Spacer is a concrete instantiation of "the
untrusted engine."

The crucial thing CHC does that exploration cannot: it does not enumerate the infinite
state space, it **abstracts** it — finding a *finite* inductive invariant covering
infinitely many states. That is the analytic step.

### 6.3 Honest hard part: state projection

Encoding *the Ruby machine* as CHCs is hopeless — the state is heap, frames and
continuations. What is tractable is a **projection** onto loop-carried scalars, so the
gating problem is a slicing/dependence analysis: *which loops carry only scalar
state?* The toy qualifies; a loop mutating `@q[state][action]` does not — its carried
state is the heap, which is where the hard cases live and where this hits the same
wall as theory-of-arrays.

One helpful asymmetry: if the projection **over-approximates**, "unreachable in the
abstraction" implies "unreachable in reality", so the *no* answer stays sound; a
witness from the abstraction may be spurious, but we replay it, so that costs nothing.
**The abstraction may be sloppy in exactly the direction that is free.**

### 6.4 The unification

The picture that emerged, and the reason to record this discussion:

> **Search enumerates trip counts; invariants summarise them.**
> Direction A generates the candidate summary (from samples, §5.1) or the
> counterexample; Direction B certifies it. Neither is a complete product alone.

Concretely, each supplies what the other lacks:

| | provides | lacks |
|---|---|---|
| **A (search)** | witnesses, certified by replay; concrete samples that *suggest* summaries | can never say "unreachable" |
| **B (invariants)** | "unreachable", certified by proof | needs someone to *supply* the invariant |

An inferred loop summary is precisely a **candidate inductive invariant**, and
`invariant_sound` is precisely the machinery for consuming one soundly. That is the
same untrusted-engine / trusted-checker split the design argues for throughout —
here applied to loop summaries rather than safety invariants.

## 7. Literature

**Verified in-session** (fetched/read 2026-07-30 – 2026-08-03):

| Work | Relevance |
|---|---|
| Torlak & Bodík, *A lightweight symbolic virtual machine for solver-aided host languages*, **PLDI 2014** ([DOI](https://dl.acm.org/doi/10.1145/2666356.2594340)) — PDF read | Symbolic unions, `for/all`, "only and all" soundness/completeness (§3.4), booleans+finite integers as the only primitive symbolic constants |
| Rosette Guide §4.9, §7 ([docs](https://docs.racket-lang.org/rosette-guide/)) | Z3 default **and bundled**; CVC4/CVC5/Boolector/Bitwuzla/STP/Yices2 optional; SMT-LIB2 over subprocess. Symbolic reflection: `union?`, `union-contents`, `for/all` |
| [emina/rosette releases](https://github.com/emina/rosette/releases) | Maintenance: 4.1 (Mar 2025), 4.0 (Mar 2024), ~annual cadence; alive but low-velocity |
| Nelson et al., *Serval*, **SOSP 2019** ([PDF](https://unsat.cs.washington.edu/papers/nelson-serval.pdf)) | Building verifiers by **lifting interpreters** under symbolic evaluation (RISC-V/x86-32/LLVM/BPF). Headline contribution is *symbolic profiling* — **blowup, not soundness, is the hard part** |
| Nelson et al., *Jitterbug*, **OSDI 2020** ([project](https://unsat.cs.washington.edu/projects/jitterbug/)) | Rosette-based verification with real impact: 16 previously unknown bugs found in five deployed Linux BPF JITs, upstreamed |
| Hildenbrandt et al., *KEVM*, **CSF 2018** ([PDF](https://fsl.cs.illinois.edu/publications/hildenbrandt-saxena-zhu-rodrigues-daian-guth-moore-zhang-park-rosu-2018-csf.pdf)) | K framework: **one declarative semantics, two backends** — LLVM (concrete) + Haskell (symbolic). Precedent for D4 |
| KLEE sources ([Memory.cpp](https://github.com/klee/klee/blob/master/lib/Core/Memory.cpp), [Expr](http://klee-se.org/doxygen/html/classklee_1_1Expr.html)) | Every value is a `ref<Expr>`; **concrete is not a separate case** (`ConstantExpr` leaf ⇒ no taint flag); memory as theory-of-arrays with a per-byte concrete fast path (`concreteStore`/`knownSymbolics`) |

**Recalled, not verified in-session** — treat citations as leads to check before
relying on details:

| Work | Relevance |
|---|---|
| Korel, *Automated Software Test Data Generation*, IEEE TSE 1990 | **Branch distance** + alternating-variable method — the origin of the "closeness" idea |
| McMinn, *Search-based software test data generation: a survey*, 2004 | Branch distance + approach level; SBST landscape |
| Chen & Chen, *Angora*, IEEE S&P 2018 | Byte-level taint + **numerical gradient descent** on branch distance, explicitly instead of symbolic execution |
| She et al., *NEUZZ*, IEEE S&P 2019 | Neural **program smoothing**; learn a differentiable surrogate, descend on it |
| laf-intel; Steelix | Split multi-byte comparisons to expose finer-grained progress signal |
| Godefroid et al., *DART*; Sen et al., *CUTE*; Godefroid et al., *SAGE* | The concolic loop we implement (concrete run + path condition + flip); SAGE's generational search |
| Avgerinos et al., *Enhancing Symbolic Execution with Veritesting*, ICSE 2014 | **State merging**: statically symbolic within bounded regions, path-based across them — the middle of the spectrum in §1 |
| Saxena et al., *Loop-extended symbolic execution*, ISSTA 2009 | Trip counts as first-class symbolic variables + linear relations — closest prior art to §3/§5 |
| Gulwani et al., *SPEED* | Symbolic complexity bounds via counter instrumentation |
| Karr 1976; Rodríguez-Carbonell & Kapur; Müller-Olm & Seidl | Affine / polynomial invariant generation (ideals, Gröbner bases) |
| Colón, Sankaranarayanan & Sipma | **Constraint-based invariant generation** (templates + Farkas) — §5.2 #7 |
| Bjørner et al., **Spacer** (in z3); Eldarica | CHC solving over infinite-state systems — §6.2 |
| Maple `gfun`/`guessRec`; Mathematica `FindSequenceFunction`; `sympy.rsolve`; OEIS | Practical sequence→closed-form tooling — §5.1 |

## 8. What this implies for sequencing

Ordered by (value ÷ cost), given everything above:

1. **Exponential trip-count probing** (§3) — ~20 lines, no new theory, turns linear
   trip-count search into logarithmic. Do it whenever the search is next touched.
2. **Finite-domain exhaustive splitting as directed goals** (§2.4) — reuses
   `DispatchRisk`; start with symbol/class-tag domains (finite by construction, no new
   solver theory). **Re-measure ai4r before committing to theory-of-arrays** — §2.3
   suggests it may not be needed for the nil-bug class.
3. **Finite-difference summary inference** (§5.1 #1) as a *search heuristic only* —
   tiny, exact on the common case, and safe by construction because witnesses are
   replayed.
4. **Deferred, needs a motivating case:** CHC/Spacer + state projection (§6).
   Justify it the way `narrowNeedle` justified Phase 2 — with a program we
   *demonstrably* cannot answer, **and where "no" is the answer that matters**. We do
   not have one yet: every bug found so far has been a "yes" reachable by search, and
   the "no" direction is currently served by hand-written invariants (T5, the dispatch
   loop). Pressure arrives when someone wants a *safety verdict* on a program whose
   invariant nobody wants to write by hand.
