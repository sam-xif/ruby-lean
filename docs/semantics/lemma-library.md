# The lemma library — certified method summaries, proposed by AI, proved in Lean

**Status: design / nothing built.** Companion to
[`search-and-proof.md`](search-and-proof.md) (whose §6.4 unification this instantiates at
method granularity), [`concolic-dataflow.md`](concolic-dataflow.md) (whose term language
the summary language reuses), and
[`../../../type-safety-by-reachability.md`](../../../type-safety-by-reachability.md)
(whose §4 untrusted-engine/trusted-checker split this is — with an LLM as the untrusted
engine).

Origin: a 2026-08-03 design conversation, continuing `search-and-proof.md`'s origin
thread. The prompting idea: instead of reasoning about `f(n)` by re-exploring its body at
every call site, *sample* what a method does, have an AI propose a candidate summary
relating inputs to outcome, **prove it in Lean against `stepFn`**, and thereafter use the
proved lemma as the method's denotation — at call sites in the concolic engine (Direction
A) and in caller invariant proofs (Direction B). Lemmas accumulate into a library; callers
quantify over callees via their lemmas instead of their bodies.

Three decisions fixed at design time (2026-08-03):

1. **Method summaries first** — the lemma unit is a method, not a loop. Loop summaries
   (`search-and-proof.md` §5) reappear *inside* this design as the inner invariants a
   method proof needs.
2. **The LLM harness is specced concretely** (§5), not left as an abstract proposer slot.
3. **Lean-proved from the start** — no lemma is consumed by anything until its
   conformance theorem is kernel-checked and axiom-clean. There is no corpus-validated
   "usable but unproved" tier; corpus validation exists only as a *falsification gate*
   before spending proof effort.

---

## 1. What a lemma is, and where it sits in the architecture

A lemma is a **certified method summary**: a machine-checked theorem that a specific
method, entered from a specific booted heap with arguments in a declared domain, reaches
its call boundary with an outcome satisfying a declared relation, touching nothing else.

This is assume-guarantee / contract-style modular verification (Houdini, Daikon,
compositional CHC — §9) with two twists that match this workspace's standing discipline:

- **Certifying, not trusted.** The proposer (an LLM) and the prover (an LLM with build
  feedback) are both untrusted; the Lean kernel is the sole admission authority. A wrong
  proposal costs time, never soundness — the same split as
  `type-safety-by-reachability.md` §4, with "abstract interpretation / IC3" replaced by
  "Claude".
- **Conditioned on the booted heap.** Ruby dispatch is a heap fact, so a summary is only
  true relative to a method-table context. Every lemma carries a **dispatch fingerprint**
  (§6.3); a program that reopens the class invalidates the lemma. This is
  `bounded-effect-checking.md` §4.2's semantic heap-diff, reused as lemma invalidation.

What the lemma buys, per direction:

| | without the lemma | with the lemma |
|---|---|---|
| **A (concolic)** | call boundary goes `opaque` — the return term is lost, downstream conditions unflippable (`concolic-dataflow.md` §6.1) | return value gets a term: conjoin `rel(argTerms, ret)` into the shadow; the call becomes solver-transparent without executing symbolically |
| **B (invariants)** | caller's invariant must enumerate every mid-callee `(ctl, kont)` shape — `T5Loop.lean`'s `J` lists the callee body's configs explicitly | caller invariant covers only *boundary* shapes; the in-callee segment is discharged by the callee's lemma via `segment_sound` (§3.3) |

## 2. The summary object

### 2.1 Scope of v1 — deliberately narrow

- **Simple-typed signatures only:** arguments and return in `Int | Bool | Nil`
  (the `SymTerm`-expressible fragment). Strings, collections, user-object arguments:
  out of scope until the term language grows sorts.
- **`pure` effect only:** heap unchanged, stdout unchanged, no globals written. §8.3
  explains why this is load-bearing (heap pinning composes only with heap-preserving
  callees) and what phase 2 relaxes.
- **Self-independent methods first:** toplevel `def`s, or methods whose bodies read no
  ivars. Methods reading `@x` need ivar preconditions in the entry config (§8.5).
- **No block parameters.** A method taking a block has a summary *parameterized by the
  block's behavior* — higher-order lemmas, deferred (§8.4). This excludes exactly the
  prelude Enumerable methods; the honest consequence is that v1 cannot summarize `map`.

Narrow is fine: the deliverable of v1 is the **loop and the composition machinery**, not
coverage. Coverage is the same ratchet discipline as everything else here.

### 2.2 The summary language — `SymTerm` plus a `ret` atom

Reuse the shadow's term language (`Concolic/Shadow.lean`: `inp`/`lit`/`un`/`bin`/`conc`/
`opaque`), extended engine-side with a distinguished `ret` atom. A summary is **guarded
and relational**:

```json
{ "method": "f", "owner": "Object", "argTys": ["int"],
  "cases": [
    { "guard": ["bin","lt",["inp",0],["lit",0]],
      "outcome": { "returns": true, "rel": ["bin","eq",["ret"],["lit",0]] } },
    { "guard": ["un","not",["bin","lt",["inp",0],["lit",0]]],
      "outcome": { "returns": true,
        "rel": ["bin","eq",["bin","mul",["lit",2],["ret"]],
                            ["bin","mul",["inp",0],["bin","add",["inp",0],["lit",1]]]] } }
  ],
  "raises": [],
  "effect": "pure",
  "innerInvariants": [ { "loc": "while-loop-1", "inv": "…" } ] }
```

Design points:

- **Relational, not functional.** `2·ret = n·(n+1)` sidesteps division (excluded from
  `SymTerm` per K7 — Ruby's flooring `/` has no clean z3 counterpart) and is what the
  solver consumes anyway. When the outcome *is* a term, `ret = t` is the special case.
  Determinism of `stepFn` means the relation, though written loosely, pins a unique
  outcome per input — weaker-to-state, easier-to-prove, equally informative.
- **Guards must be exhaustive and disjoint over the declared domain** (checked
  mechanically by z3 before the proposal proceeds — Rosette's "only and all" discipline
  from `search-and-proof.md` §2.1, applied to the summary's own case split).
- **`raises` cases are first-class:** `{ "guard": …, "raises": "TypeError" }`. A summary
  that only covers the happy path cannot serve type-safety analysis — a caller may
  `rescue`, and "raised ≠ stuck" (`type-safety-by-reachability.md` §2) means the raising
  case is *delivered at the boundary*, not treated as a bad end.
- **`innerInvariants` ride along.** If the body loops, the conformance proof needs a loop
  invariant; the proposer proposes it in the same package (§8.2). This is where
  `search-and-proof.md` §5's summary-inference menu (finite differences, template+SMT)
  plugs in — as *sub-proposers* feeding the method-level proposal.

## 3. The Lean side — statement template and composition metatheorem

New files: `RubyCore/Proof/Summary.lean` (the template, once) and
`RubyCore/Proof/Lemmas/<Name>.lean` (one per lemma, generated).

### 3.1 Entry configuration

A lemma quantifies over *call contexts* and pins the *callee activation*. Following
`T5Loop.mkNext`'s post-dispatch shape:

```lean
/-- The machine is at the entry of `spec`'s body: activation frame just pushed,
    caller continuation `K` and caller stack `rest` arbitrary. -/
def Entry (spec : MethodSpec) (args : List Value) (H : Heap)
    (m : Machine) (fid : FrameId) (K : List Kont) (rest : List FrameId) : Prop :=
  m.ctl = .eval spec.body ∧
  m.kont = .frameK fid :: K ∧
  m.stack = fid :: rest ∧
  m.frames.getD fid default = spec.activation args ∧
  fid = m.frames.size - 1 ∧ 0 < m.frames.size ∧
  m.heap = H            -- v1: heap pinned to the lemma's booted heap (§8.3)
```

The quantification over `K` and `rest` **is the modularity**: nothing in-body touches
konts below the `frameK` marker except non-local jumps, which the outcome cases cover.

### 3.2 Conformance — the per-lemma theorem (generated, then proved)

```lean
/-- `spec` conforms: from any entry config, execution reaches the call boundary
    with the declared outcome, and the caller's world is untouched. -/
def Conforms (spec : MethodSpec) (H : Heap) : Prop :=
  ∀ m fid K rest args, Entry spec args H m fid K rest → spec.inDomain args →
    ∃ m', Reaches m m' ∧
      m'.kont = K ∧ m'.stack = rest ∧            -- back at the boundary
      spec.outcomeHolds args m'.ctl ∧            -- value v with rel(args,v), or
                                                 -- .jump (.raiseJ exc) with classOf ∈ declared
      m'.heap = m.heap ∧ m'.out = m.out ∧        -- v1 `pure` frame condition
      FramesPreserved m m'                       -- caller-visible frames unchanged
                                                 -- (store may grow — cf. T5Loop)
```

Notes:

- This is a **total**-correctness form — `Reaches` a boundary config, so the lemma also
  certifies termination of the call. That is deliberate given the Lean-proved-from-the-
  start decision: since `stepFn` is a *function*, a total lemma pins the entire in-call
  trace, and safety of every intermediate config is a corollary (any config on the chain
  steps via `.next`, hence is not `aboutToTypeStick`). One theorem, three uses: return
  term for A, segment safety for B, termination for free.
- A **partial** form (invariant confinement: any config reachable with `fid` still on the
  stack satisfies `Inv`, and none is `aboutToTypeStick`) is specified as the fallback for
  bodies whose termination we cannot prove. It serves Direction B but yields no return
  relation. v1 implements total only; partial is a recorded extension.
- `FramesPreserved m m'` := `m.frames.size ≤ m'.frames.size ∧ ∀ i < m.frames.size,
  i ≠ fid → m'.frames.getD i default = m.frames.getD i default`. Frame-store growth
  without reclamation is a fact of the machine (`T5Loop` header) — the condition says the
  *caller-visible* entries are stable, which is what `getD0_push`-style lemmas discharge.

### 3.3 `segment_sound` — the composition metatheorem (the genuinely new metatheory)

`invariant_sound`'s Consecution quantifies over *every* reachable config, including
mid-callee ones — which is why `T5Loop.J` had to enumerate the callee body's shapes. The
lemma library needs the one-time metatheorem that lets a caller invariant *skip* certified
segments:

```lean
/-- Caller-level invariant J + certified segments ⇒ safety.  Every J-config either
    (a) steps to a J-config and is not aboutToTypeStick, or (b) is an Entry config of
    some proved spec whose boundary config (given by Conforms) is again a J-config.
    Then no reachable outcome is type-stuck. -/
theorem segment_sound … : ∀ r, ReachableResult m₀ r → ¬ typeStuck r
```

Proof sketch: strong induction along `Reaches`; in case (b), determinism of `stepFn`
means the reachable chain *through* the segment is exactly the chain `Conforms`
exhibits, every config on it steps (hence safe), and the induction resumes at the
boundary. This theorem is proved **once**, next to `invariant_sound` in
`Proof/Summary.lean`. It is the single riskiest artifact in the design and therefore the
first milestone (§7, M0): if `segment_sound` is awkward to state or use, the composition
story changes shape, and better to learn that before any harness exists.

## 4. The loop — pipeline stages

```
select target → sample → propose (LLM) → falsify (cheap) → compile statement
      → prove (LLM + lake) → axiom audit → admit to library → consume
```

1. **Select.** Demand-driven, from the frontiers already emitted: a `DispatchRisk` /
   `opaque`-at-call-boundary note in a concolic run, or a Direction-B proof attempt
   stalling on a dispatch case. Each becomes a `summary-wanted(owner, method)` request.
   No speculative sweeping in v1 — the library grows where search actually hurts.
2. **Sample.** Wrapper program `<corpus file(s)> ; f($__in0, …)` run through the existing
   tracer entry (`ConcolicMain` with `--inputs`, the `$__inK` mechanism of
   `concolic-dataflow.md` §6.5 — no new machinery). ~16–32 samples: small values, sign
   boundaries, plus solver-guided points near proposed guard boundaries on iteration.
   Record per sample: args, outcome (value or exception class), stdout delta, and a
   heap-changed bit (any change ⇒ not `pure` ⇒ out of v1 scope, reject early).
3. **Propose.** The LLM emits the §2.2 JSON (schema-validated). See §5.
4. **Falsify.** Before any proof effort: (i) replay the relation against all samples;
   (ii) check guard exhaustiveness/disjointness with z3; (iii) adversarial sampling —
   solve for args satisfying a guard but *violating* its relation, run them, see if the
   violation is real. Rejections loop back to the proposer with the counterexample.
   **This gate admits nothing** — it only prevents wasted proof attempts.
5. **Compile.** Deterministic codegen (no LLM): summary JSON → `Proof/Lemmas/<Name>.lean`
   containing the pinned heap (built by reducible `alloc`s from `Boot.initHeap` +
   the corpus file's class defs, exactly the `T5Loop.Hstar` pattern), the `MethodSpec`,
   and the `Conforms` theorem with the proof left open.
6. **Prove.** The LLM prover agent (§5.3) fills the proof; `lake build` is the referee.
7. **Audit.** `#print axioms` gate, same discipline as impl-notes L13: `propext`,
   `Classical.choice`, `Quot.sound` only — no `sorryAx`, no `native_decide`. Mechanical.
8. **Admit.** Commit the `.lean` file; append to `lemmas/manifest.json`: summary JSON +
   theorem name + dispatch fingerprint (§6.3). The manifest is the diffable, reviewable
   artifact — same trust posture as the mock manifest
   (`type-safety-by-reachability.md` §10.4).

## 5. The LLM harness

Lives in `ruby/lemmas/` (sibling of `concolic/`): a Python driver reusing
`concolic/concolic/terms.py` for term evaluation and z3 translation, plus `bin/lemma-loop`.

### 5.1 Proposer

- **One call per candidate, structured output** (the §2.2 JSON schema, enforced).
- **Context pack:** (a) the method's Ruby source and its RubyCore export; (b) the
  samples table; (c) the term-language grammar and the "relational form encouraged,
  division unavailable" rules; (d) two accepted summaries as few-shot examples; (e) on
  retry, the falsification counterexample from stage 4.
- **Sub-proposers run first and are included in the pack as hints:** Newton
  forward-differences over the samples and OEIS-shaped lookup (`search-and-proof.md`
  §5.1 #1/#5) are ~free and often *are* the answer; the LLM's marginal value is guards,
  raise cases, and inner invariants.
- Budget: ≤4 propose–falsify iterations per target, then park the target with its
  samples (a parked target is a frontier report, not a failure).

### 5.2 What the proposer never does

It never touches Lean, never sees the proof, and its output is never consumed by anything
but the falsification gate and the statement compiler. Prompt-injection-shaped concerns
(corpus code influencing the proposal) are inert: a malicious proposal is just a false
conjecture, and it dies at the kernel.

### 5.3 Prover agent

- An agentic LLM session per lemma with exactly three capabilities: read the generated
  `Lemmas/<Name>.lean` + a fixed set of reference files (`Proof/Summary.lean`,
  `T5Loop.lean`, `DispatchLoop.lean` as proof-idiom few-shots), edit the proof region,
  and run `lake build` (+ the axiom audit script).
- The generated file constrains the degrees of freedom: the statement is frozen (edits
  to anything outside the proof region are rejected by the driver, not by convention).
- Budget: wall-clock and attempt caps per lemma; on exhaustion the lemma parks with its
  best partial proof for human attention. Expected to be the expensive stage; the
  library is append-only and keyed by fingerprint, so cost amortizes across every future
  run that hits the same method.
- **Tactic support is the real leverage** (§8.1): a `step_shape` tactic packaging the
  `simp only [stepFn, evalExpr, applyKont, …]` chains that `T5Loop.stepJ` writes by hand,
  so straight-line body segments discharge mechanically and the agent spends its budget
  on branches and loop invariants only. Building this tactic is in scope for M2.

## 6. Consumption

### 6.1 Direction A — call-site terms in the concolic engine

At the dispatch point (last-`argsK` handling, `Shadow.lean`), when `(classOf recv,
mname)` matches a manifest entry whose fingerprint matches the current booted heap and
whose argument terms are non-`opaque`: allocate a fresh solver variable `r` for the
return value, conjoin the matching case's `rel(argTerms, r)` and its guard into the path
condition, and set `ctl`'s term to `r`. The `raises` cases become flippable goals — "make
this call raise" is now a solver query, which is `DispatchRisk` generalized.

**Self-check extends** (`concolic-dataflow.md` §6.4): the concrete return value must
satisfy the relation at the concrete args, checked on every run. For a *proved* lemma a
failure should be impossible — so a failure is loud and diagnostic (fingerprint bug,
manifest/theorem drift), not a silent precision loss.

### 6.2 Direction B — composed invariant proofs

A caller's invariant lists boundary shapes only; its Consecution obligation at the
dispatch step cites the callee's `Conforms` through `segment_sound`. Concretely, the T5
family gains a two-method variant (M0's second deliverable) where the caller proof is
~the size of `T5Loop` despite the callee body being opaque to it.

### 6.3 Fingerprints and invalidation

A lemma's proof depends on finitely many resolution facts (which `MethodDef` each send
in the body resolves to, over the pinned heap). The fingerprint records that
dispatch-relevant slice: for each (receiver class, method) the proof used — owner,
method-def hash, ancestor chain. At consumption time the engine recomputes the slice
against the *actual* booted heap; any mismatch (reopened class, `prepend`, shadowing
`def`) disables the lemma for that program. Conservative and cheap; this is the semantic
heap-diff of `bounded-effect-checking.md` §4.2 doing double duty, exactly as predicted
there for incrementality.

## 7. Sequencing

Ordered so that the riskiest, cheapest-to-test artifact comes first, before any harness:

| | Milestone | Content | De-risks |
|---|---|---|---|
| **M0** | Composition proved by hand | `Proof/Summary.lean`: `Entry`/`Conforms`/`FramesPreserved` + **`segment_sound`**; hand-prove one real summary (a triangular-sum `f(n)` with a `while` loop — exercises inner invariants) and one caller theorem composed through it | the statement template and `segment_sound` — everything else depends on their shape |
| **M1** | Sampling + falsification | wrapper-program driver over `ConcolicMain --inputs`; summary JSON schema; sample replay + z3 guard checks + adversarial sampling | none of it novel; reuses concolic plumbing |
| **M2** | Statement compiler + `step_shape` tactic | deterministic codegen to `Proof/Lemmas/`; the stepping tactic that mechanizes T5Loop's simp chains | proof cost per lemma (the binding constraint per Serval's lesson) |
| **M3** | LLM proposer + prover | §5 harness, budgets, axiom gate, manifest | loop closes end-to-end on the M0 example *re-derived automatically* — the acceptance test |
| **M4** | Consumption | engine-side relation conjunction + self-check + fingerprints; first composed Direction-B proof citing a machine-produced lemma | the payoff |

Deferred, in rough order of expected pressure: heap-extension effects with
resolution-fact-preservation (§8.3); ivar preconditions (§8.5); partial-form lemmas for
nonterminating-or-unprovable bodies (§3.2); block-parameterized summaries (§8.4); CHC/
Spacer as an alternate proposer whose returned invariant feeds the same compiler
(`search-and-proof.md` §6.2 — same pipeline, different untrusted engine).

## 8. Honest hard parts (ranked)

1. **Proof cost is the binding constraint.** `T5Loop` spends ~200 lines on a one-line
   body via explicit shape enumeration. That does not scale by hand and scales only
   moderately by LLM; the `step_shape` tactic (M2) is the highest-leverage single
   artifact after `segment_sound`. If the tactic proves hard, the fallback is worse
   proofs, not a different architecture — but expect this to bound throughput. (Serval's
   lesson again: blowup, not soundness, is the hard part.)
2. **Loops inside bodies re-import the invariant problem.** Every in-body loop needs an
   inductive invariant in the proof. The proposer proposes them (§2.2), finite
   differences supply the common shapes, template+SMT is the upgrade path — but a wrong
   inner invariant is only discovered at proof time, the expensive stage. Expect the
   propose→prove iteration count to be dominated by this.
3. **Heap pinning limits composition.** v1 pins `m.heap = H` and requires `pure`, so
   chains of summarized calls stay at `H` — consistent, but it excludes any allocating
   method (in Ruby, that is most methods; even integer-returning ones often allocate
   intermediates). Phase 2 replaces the pin with hypotheses (the resolution facts of the
   fingerprint) plus a heap-extension relation and a once-proved "resolution facts are
   stable under extension" lemma. That is real metatheory work; scheduling it before the
   library has demonstrated value would be premature.
4. **Blocks.** A summary for `m(&blk)` is a function of the block's behavior —
   higher-order lemmas quantifying over a block spec. Deferred, but note the sharp
   consequence: the prelude Enumerable methods, the single most valuable summary targets
   by call frequency, are exactly the ones v1 cannot express.
5. **`self` and ivars.** Methods reading `@x` need the entry config to constrain the
   receiver's ivars, which drags object state into the summary language (a `self.@x`
   atom, plus heap-read facts in the proof). Tractable — it is still finite concrete
   state under a pinned heap — but it widens every stage of the pipeline, so it waits
   for a motivating target.
6. **Boundary-local bugs are not witnesses.** A `raises` case reachable *given the
   summary's domain* says nothing about whether any real caller reaches it with such
   args. Standing rule, unchanged: nothing is reported until an end-to-end input replays
   through `stepFn` (and CRuby). Compositional analysis proposes; whole-program replay
   disposes.

## 9. Prior art (recalled, not verified in-session — check before relying on details)

| Work | Relevance |
|---|---|
| Flanagan & Leino, *Houdini*, 2001 | guess-and-check annotation inference — the propose→check loop shape |
| Ernst et al., *Daikon* | invariant candidates from execution samples — our stage 2→3 |
| Compositional CHC (Spacer; Hoder & Bjørner) | procedure summaries as uninterpreted predicates the solver fills — the same lemma library, discovered rather than proposed; our future alternate proposer |
| Assume-guarantee reasoning; Dafny/Why3 contracts | callers reasoning over callee specs, not bodies — §6.2 |
| Godefroid, *Compositional dynamic test generation* (SMART), POPL 2007 | function summaries inside a concolic engine — §6.1's use, minus the proof |
| Si et al., *Code2Inv*; recent LLM-invariant work (e.g. Wu et al. 2023–24) | learned/LLM invariant proposal with a sound checker — the §5 harness's genre |

## 10. Relation to the standing theses

- **One checker, pluggable predicate** — unchanged; lemmas are inputs to it, not a new
  checker.
- **Untrusted engine / trusted validator** — the LLM is the most-untrusted engine yet
  admitted, and needs no new argument: the kernel was always the boundary.
- **Search and proof supply each other** (`search-and-proof.md` §6.4) — here the samples
  (search) *suggest* the summary and the proof *certifies* it, per method instead of per
  loop; and each admitted lemma feeds back into search as solver-transparent call sites.
  The library is the memoization of that exchange.
