# User stories: what a partial semantics buys an end user

A framing artifact for the whole investigation (Ruby in [`./`](AGENTS.md), POSIX in
[`posix/`](posix/AGENTS.md)). It answers two questions that target selection alone does
not: **given a semantics, what does it enable an end user to do?** and — since the
overarching goal is *adversarial robustness against advanced AI* — **how can a partial
formalization of the world give users asymptotic confidence?**

The operationalization of the flagship story (a commit-time bounded effect checker) is
worked out separately in [`bounded-effect-checking.md`](bounded-effect-checking.md).

---

## 1. The objection this document answers

Formalizing the entire world is impossible. A semantics of Ruby proves nothing with
certainty about a real execution unless the interpreter, the machine code it JITs to, the
OS interface, and ultimately the hardware are also verified. Naively, verification is a
chain that is only as strong as its weakest link — so why formalize any one layer?

## 2. The reframe: formalize the layers the adversary must pass through

Adversarial robustness is a different game from deductive certainty. What matters is
**where the adversary's artifact lives and which interfaces its effects must flow
through** — the threat model, not the stack depth, determines which layers need semantics.

If the threat is *an advanced AI writing or modifying Ruby code* (the realistic near-term
model), the adversary is **confined to the same layer the semantics models**. It does not
get to write C; every trick must be expressible in Ruby surface syntax, and a faithful Ruby
semantics characterizes that entire action space. The unverified interpreter underneath is
*shared trusted substrate* — defender and adversary stand on it equally. This is the seL4
lesson inverted: assumptions don't invalidate a guarantee, they **localize the attack
surface**, and a localized attack surface is the win.

Two layers are worth owning, and they are exactly our two investigations:

1. **The artifact layer** (Ruby) — where the adversary's code lives. The semantics
   characterizes what any program *can mean*. Fidelity of the dispatch/metaprogramming
   model matters most, because that is where Ruby backdoors hide (`method_missing`,
   `const_missing`, coercion protocols, `prepend`).
2. **The effect choke point** (POSIX) — where consequences touch the world. Nothing
   persistent or external happens except through syscalls. A partial formalization *at a
   choke point* yields global guarantees about effects even with an unverified interior:
   "whatever this code computes, its filesystem footprint is confined to X" is checkable
   at the interface without understanding the computation.

**The two targets are not competitors; they are the two ends of one confinement
argument.** This reframes the week's target-selection question (see §8).

## 3. How a partial model attaches to reality without proof

The model–reality gap is never closed deductively. It is **measured and monitored**:

- **Differential testing** (already running — the desugar harness ratchet) makes the
  divergence set an empirically shrinking, coverage-measured object.
- **Adversarial differential testing** is the asymptotic mechanism: a strong red-team AI
  *searches* for model–reality divergences; the failure rate of the best available
  attacker is the robustness measure, ratcheting monotonically as found divergences are
  fixed. Confidence is asymptotic *in adversary strength* — the right parameter when the
  threat is advanced AI. AI progress cuts both ways: stronger adversaries are also
  stronger divergence-hunters working for the defender.
- **Runtime monitoring** is the trump card: run the model interpreter alongside production
  (the `obs⁺` harness is a prototype). The model need only be correct on *executed
  traces*, checked online; any divergence on a real execution is *detected*, converting a
  soundness gap into an alarm. The adversary must find an input where model and reality
  diverge *silently* — precisely the set being adversarially shrunk.

## 4. The user stories

### US1 — Robust regression suite synthesis (bounded observational-equivalence checking)

Not "generate more tests" but: given `P` and an AI-proposed `P′`, use the semantics to
check `obs(P) = obs(P′)` up to bounds, or produce a **witness input** where they diverge.
The regression suite is the accumulated set of divergence witnesses — robust in a way
sampled tests cannot be, because it is derived from the semantics of the diff rather than
drawn from a distribution the adversary can predict.

The critical upgrade over line coverage is **semantic-branch coverage**: a suite
synthesized to cover dispatch outcomes and rule firings closes exactly the hiding places
(`method_missing` fallbacks, coercions, hook methods, encoding edge cases) that line
coverage cannot see. Witnesses are *model-independent* once confirmed on real CRuby;
equivalence verdicts inherit model fidelity (§3), which is why the difftest ratchet is the
foundation, not scaffolding.

### US2 — Semantic diff review

For a proposed change, emit the *derivation-level* delta: "this diff causes dispatch of
`save` to resolve through a new module — here is the rule-by-rule trace." A reviewer
(human or AI) checks meaning, not text. Metaprogramming-based obfuscation — the natural
adversarial move in Ruby — is exactly what the heap-mutation dispatch model makes legible:
a backdoor *is* a heap delta, visible even when the textual diff looks inert.

### US3 — Effect-confinement certificates

At the POSIX layer: "this program's syscall trace, under all executions within bounds,
touches only these paths / never `exec`s / never opens a socket." The guarantee an agent
sandbox wants, expressible entirely at the choke point, robust to arbitrary weirdness in
the unmodeled interior. Operationalized in
[`bounded-effect-checking.md`](bounded-effect-checking.md). This is the strongest
*product* story for the POSIX substrate work.

### US4 — The trusted-monitor architecture (composition of US1–US3)

AI writes code → semantic diff review (US2) → equivalence/effect check (US1/US3) → runs
under a POSIX-level monitor holding a confinement certificate → any model–reality
divergence at either layer raises an alarm rather than silently passing. Each layer is
partial; the *composition* forces the adversary to defeat all layers simultaneously,
including finding silent divergences in two independently-ratcheted models.

## 5. Check vs. prove: the two effort levels

A key structural point (it reshaped US3 into the architecture below): the fuel-bounded
interpreter and the inductive step relation serve *different* verbs, and the adequacy
proof between them is what lets trust flow.

- **Bounded checking** (fuel k₁, path depth k₂, context/data size k₃): push-button,
  always terminates, verdicts of the form "no witness within the frontier (k₁,k₂,k₃)."
  Needed when arbitrary adversarial diffs must get a verdict in bounded time — the
  adversary can always contrive code that defeats invariant synthesis, so bounded search
  is the automation floor. Undecidability (Rice) is managed by truncating two infinities:
  execution length (fuel) and input space (symbolic path search / bounded enumeration),
  plus for Ruby a third — the *program contexts* that could later monkey-patch what the
  diff touches.
- **Unbounded proof by induction over the step relation**: safety properties (confinement
  is one — "no reachable configuration emits an effect outside S") are provable for
  executions of every length, no fuel anywhere. The undecidable core relocates into
  *finding the inductive invariant* (for equivalence of two programs, a bisimulation —
  invariant discovery squared).
- **Proof-carrying code dissolves the tension**: in the adversarial-AI setting, *demand
  that the submitted diff arrive with a machine-checked confinement proof over the step
  relation*. The untrusted, capable submitter bears the undecidable burden (find the
  invariant); the defender's checker is Lean's kernel — decidable, fast, tiny trusted
  base. Refusal to prove is itself signal. The economics that killed PCC in the 1990s
  (proof authoring was brutally expensive for humans) are exactly what advanced AI
  reverses. This inverts the asymmetry that usually favors the attacker.

Division of labor: **unary safety (confinement) → unbounded inductive proofs,
adversary-supplied; relational properties (obs-equivalence of diffs) → certified bounded
search** as the automatic floor. Same relation, same checker, two effort levels.

Adequacy (interpreter ↔ relation, PROJECT_PLAN §5.1) is load-bearing here: differential
testing earns trust for the *interpreter*; proofs live on the *relation*; the adequacy
theorem transfers the empirical trust across. Without it we would test one artifact and
prove things about another.

## 6. What "asymptotic confidence" cashes out as

Not `P(safe) → 1` distributionally — the adversary picks the input. Rather: **the
adversary's search problem gets monotonically harder along measured dimensions**:

1. model–reality agreement under the strongest known attacker (§3);
2. semantic coverage of the synthesized suite / verified frontier (k₁,k₂,k₃) (US1, US3);
3. fraction of the effect surface behind monitored choke points (US3/US4);
4. fraction of claims carrying unbounded, adversary-supplied proofs (§5).

Each is a ratchet of the kind already running in the desugar harness. Any backdoor is
pushed into regions that are increasingly expensive, contrived, and — for the human-review
layer — increasingly weird-looking.

## 7. Honest limits

- **Model fidelity is empirical and finite.** Even an unbounded inductive proof covers the
  *model's* step relation; attachment to CRuby-on-Linux is a finite corpus. Proofs don't
  shrink the fidelity gap — they make it the *only* gap, which is what makes the
  adversarial-difftest ratchet the permanent foundation.
- **Safety only, on the induction recipe.** Liveness/termination claims need well-founded
  measures; fuel-boundedness genuinely re-enters there.
- **Below-the-layer attacks** (supply-chain on the interpreter, hardware) are explicitly
  out of scope — by design: the formalization's job is to force the adversary out of the
  cheap, deniable layer (source that passes review) into expensive, conspicuous ones.

## 8. Consequence for target selection

This framing changes what to optimize for: **fidelity of the dispatch/metaprogramming
model** (where Ruby backdoors hide) and **the syscall boundary** (where effects are
confined) — over breadth of stdlib coverage. It also recasts the Ruby-vs-POSIX question:
the *product* is the checker/monitor stack (US4), the Ruby semantics is its executor, and
the POSIX layer is its policy vocabulary. One system, not two candidate targets. The
POSIX untreated-segments analysis ([`posix/directions.md`](posix/directions.md)) then
matters mainly insofar as a sandbox monitor must not be evadable through the untreated
substrate (signals, `fork`, job control) — a sharper selection criterion than novelty
alone.
