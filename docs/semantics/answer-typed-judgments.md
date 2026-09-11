# Answer-typed judgments — one root cause behind four separate walls

> **Status:** findings artifact, 2026-09-10/11; **§6's decomposition layer BUILT 2026-09-11
> — see §10**, which also corrects §6 and closes two of §8's four open questions. Every claim
> below is either mechanised (named theorem, axiom-clean) or measured against CRuby 4.0.5 /
> `srb` 0.6.13405.
>
> Evidence tags per [`README.md`](README.md): **[V]** verified in this workspace,
> **[M]** mechanised in Lean here, **[D]** documentation or literature, **[?]** open,
> **[✗→]** a correction of a plausible-but-false claim made earlier in the same
> investigation, recorded so it is not reintroduced.
>
> Companions: [`types-and-preservation.md`](types-and-preservation.md) §B surveys type
> soundness and says nothing about *control*; this is that gap.
> [`lean-model-sketch.md`](lean-model-sketch.md) §1.1/§What-we-reject is the earlier
> decision this document deliberately does **not** overturn (§5).

---

## 1. The thesis

Four obstructions were hit in one investigation, in four different layers, and they
looked unrelated. They are one fact:

> **The semantic judgment reads only the `.value` arm of `RunResult`.**

```lean
-- ratchet/Denote/Sem/State.lean
def Evals (m : Machine) (e : Expr) (v : Value) (m') : Prop :=
  ∃ fuel, Interp.run fuel (evalFrom m e) = .value v m'
```

`Interp.run` answers five ways — `.value`, `.uncaught`, `.unsupported`, `.outOfFuel`,
`.stuck`. `Evals` keeps one and discards the rest, and every rule's semantic obligation
is an implication with `Evals` on the **left**. So a program that escapes satisfies every
obligation vacuously, and every attempt to reason compositionally about escape has to
reintroduce, by hand and per continuation, the information that projection threw away.

The literature's universal answer (§3) is that **an escape belongs to the answer, not to
the step**. RubyCore has that answer type already, at the run level, and drops it at the
judgment level. That is the whole diagnosis.

---

## 2. The evidence chain

Five measurements, in the order they were taken. Each is an artifact in the tree.

### 2.1 Stuck-freedom does not follow from the value axis **[M]**

`SemJudge` (`ratchet/Denote/Sem/Judge.lean:171`) concludes about `v` and `m'` *given*
`Evals m e v m'`. Three of the 48 discharged rungs are discharged **because the run does
not produce a value**: `regexpLit`'s `.unsupported` arm ("the obligation's hypothesis is
unsatisfiable and the case costs nothing"), and `callNever`/`primNever`, "discharged by
contradicting the run". The cases where the value ladder pays nothing are exactly the
cases stuck-freedom must pay everything for.

The sharpest instance: `Judge`'s `raise` rule carries `excName?`, whose docstring says
*"the premise is `excName?`, and it is soundness — `raise 5` raises `TypeError`, which is
inside the family"*. That premise is a pure stuck-freedom condition, and **no obligation
of `SemJudge`'s shape can consume it**, because a raising run never reaches `.value`. The
premise could be deleted and the semantic ladder would not notice.

Structurally: `SemJudge` has real *preservation* content (its conclusion re-establishes
`StateOk`) and **no progress content at all**.

### 2.2 One rung of the second axis is cheap — `Judge.vasgn` **[M]**

`ratchet/Denote/Rules/VasgnStuck.lean`, axiom-clean. Cost:

| component | code lines | scope |
|---|---|---|
| `stuckFreeRun_pushK_le` | 92 | one-time, every rule that pushes a continuation |
| `jumpStuckFree_asgnK` | 22 | per continuation |
| `deliver_asgnK_stuckFree` | 12 | per continuation |
| **`SemStuck.Judge.vasgn`** | **16** | the rung |

Two findings. The obligation **mentions none of the rule's typing premises** —
`Judge.vasgn` carries `capStale`/`capStaleCtx`/`isAliasTy` and the value proof spends all
three; the stuck obligation spends none and does not even need `StateOk`. And it needed
exactly one new decomposition, because `run_split` splits a run **at the value it
delivers** and therefore says nothing about the runs this axis is about.

### 2.3 At a back edge the two axes couple, and a side condition turns out false **[M]**

`ratchet/Denote/Rules/WhileStuck2.lean` proves `Judge.while'` on the stuck axis **modulo
two jump hypotheses**, by induction on *fuel*. Three results:

- **The axes are coupled here.** Re-entering the loop needs the next iteration to start
  at a conformant machine, and that fact is `SemJudge`'s third conjunct. `vasgn` needed
  no value-axis premise; `while'` needs two. **[✗→]** an earlier claim in this
  investigation that a second ladder would be independent of the first holds for
  straight-line code and fails at the first back edge.
- **[✗→] `JumpStuckFree [whileCondK …]` is false, not unproved.** `unwind`'s `nxtJ` and
  `redoJ` arms re-enter the loop *at `m`*, and re-entry needs `StateOk κ Γ I m`, which the
  side condition cannot carry — by design, since `jumpStuckFree_asgnK` did not need one.
  Counterexample: `m` whose locals disagree with `Γ`, `ctl = .jump (.nxtJ .nil)`,
  `kont = []`; its own run escapes to `.stuck`, so the hypothesis holds, while the filled
  run re-enters the loop at a non-conformant machine.
- **[✗→]** No "the sub-run consumes ≥ 1 step" lemma was needed: the two continuation
  deliveries pay for the induction on their own.

### 2.4 Iris's bind rule is unavailable, and it is provably unavailable **[M]**

`lean/RubyCore/HCtx/Bind.lean` (own lib, off the default target). Four results:

- **J36's `Language` instance cannot bind at all**: its `Val` is `ROutcome`, a
  *whole-program* answer carrying `(value, heap)`, and `wp_bind` needs `K (ofVal v)` to be
  the computation *resumed* with `v`. A binding instance needs "answer in flight plus
  ambient control state"; `instLanguageCfg` is that instance and is fine.
- **`ctx_law3_fails`** — `¬ Language.Context (fillK [.asgnK .lvar x])`. Law 3
  (`primStep_fill_inv`) says stepping a filled configuration never disturbs the context.
  `unwind` disturbs it: it pops frames belonging to `K`. The successor of `K e` is `e`,
  which has an empty continuation, and no `K e'` does.
- **The jump-as-value repair is blocked by `val_stuck`**: values may not step, and
  `retJ_steps_at_empty` exhibits a jump that does.
- **Even law 2 needs a hypothesis the class cannot hold**: `law2_of_stepFn_frame` is
  `RubyCore.Proof.stepFn_frame`, which requires `CatchFree Ks` (a condition on the
  context, statable) **and** `hside` (a condition on the expression, not statable —
  `Context K` quantifies over all `e`).

### 2.5 The continuation census: there is no jump-free sub-language **[V]**

Prompted by the objection that top-level `break`/`next` are syntax errors in Ruby — which
is correct, and initially appeared to make §2.4's witness vacuous.

**13 of 49 `Kont` constructors have a dedicated `unwind` arm** (`whileCondK`,
`whileBodyK`, `forStartK`, `forBodyK`, `frameK`, `blkFrameK`, `definedGuardK`, `catchK`,
`beginBodyK`, `rescMatchK`, `rescueK`, `elseK`, `ensureK`); the other 36 fall into the
catch-all. For those 36, two questions:

**Syntactic jumps** — Ruby's *void value expression* rule confines
`break`/`next`/`redo`/`retry`/`return` to statement position. Nineteen source positions
tested, each with the jump wrapped in `while true; …; end` so it is contextually legal:

| position | kont | parses? |
|---|---|---|
| `break; 1` | `seqK` | **yes** |
| `x = break`, `X = break` | `asgnK`, `casgnK` | no — *Invalid break* |
| `if break then 1 end`, `(break).foo`, `foo(break)` | `ifK`, `recvK`, `argsK` | no |
| `[break]`, `[*(break)]`, `{(break) => 1}`, `{1 => break}` | `arrK`, `arrSplatK`, `hshKeyK`, `hshValK` | no |
| `foo(a: break)`, `yield(break)`, `super(break)`, `break(break)` | `kwPairK`, `yieldArgK`, `superArgK`, `jumpValK` | no |
| `def f(a = break)`, `(break)::Foo`, `class Foo < (break)` | `optDefK`, `cpathK`, `classDefK` | no |
| `defined?((break).foo)`, `while (break); end` | `definedRecvK`, `whileCondK` | no |

So `seqK` is the lone survivor, and `ctx_law3_fails_seqK` is the version with a
grammatically real witness.

**Dynamic jumps** — `raise` and `throw` are **methods, not syntax**, so no void-value rule
touches them. `x = (raise "boom")`, `foo(raise("boom"))`, `[raise("boom")]`,
`(raise "boom").foo`, `if raise("boom") then 1 end`, `{1 => raise("boom")}`,
`def f(a = raise("boom"))`, `x = (throw :t)` — **all parse** [V]. And `raiseErr` leaves
the continuation alone, so `x = raise("boom")` really does put a `raiseJ` in flight with
`asgnK` innermost (`ctx_law3_fails_raise`).

**[✗→]** A hybrid — Iris bind for grammar-protected continuations, hand-rolled
decomposition for the rest — was proposed on the strength of the syntactic-jump table and
is **not available**: the grammar exempts five of the seven jump constructors and neither
of the two that ordinary code produces.

---

## 3. Prior art: everyone answers this the same way

### 3.1 The Essence of Ruby (Ueno, Fukasawa, Morihata, Ohori, APLAS 2014) **[D]**

Big-step natural semantics; object and control calculi joined by oracle relations. All
three jump kinds are **ML-style generative exceptions**:

- exception context `T`: jump kind ↦ exception **tag** `t`;
- **packed value** `[v]^t` — a raised exception with tag and parameter;
- **`result r ::= v | [v]^t | wrong`**;
- two judgment forms, `S,B,E,T ⊢ e ⇓ r, S'` and `S,B,E,T ⊢ e handle t ⇓ r, S'`;
- `JUMP`: `e ⇓ v`, `T ∋ {j ↦ t}` ⟹ `j e ⇓ [v]^t`. `CATCH`: `e ⇓ [v]^t` ⟹ `e handle t ⇓ v`;
- `PROC`/`YIELD`/`CALL` each mint a **fresh** tag and install the binding;
- and, load-bearing: *"each rule in the standard form comes with an exception propagation
  rule: if a component yields an unexpected raised exception, then it cancels any
  subsequent evaluation of other components and the entire term will yield the raised
  exception."*

Generativity is forced by their §2 `foo` example: a recursive method's `break` targets a
different activation each call, so destinations cannot be statically labelled.

### 3.2 The same move elsewhere **[D]**

| work | the escape is… |
|---|---|
| λ_JS, *The Essence of JavaScript* (Guha et al., ECOOP 2010) — Essence-of-Ruby's own inspiration | `label l e` / `break l e`, with `E[break l v] → break l v` for `E` not binding `l` |
| Wright–Felleisen-style small-step with exceptions | `E[raise v] → raise v` for handler-free `E`; soundness stated over answers = values **plus** uncaught exceptions. Note this rule *discards the context* — §2.4's law-3 violation, accepted deliberately as a redex-with-context |
| CakeML / functional big-step (Owens, Myreen, Kumar, Tan, ESOP 2016) | `result = Rval v \| Rerr (Rraise v \| Rabort a)`; mechanised, clocked — the closest fit to `Interp.run` |
| Monadic / algebraic effects (Moggi; Plotkin–Pretnar) | `Either`; bind short-circuits **by construction**, so the bind law is definitional |
| Double-barrelled CPS (Thielecke) | one continuation per exit — the compiler view, and what YARV's catch tables are |
| Hazel (de Vilhena & Pottier, POPL 2021) | a WP indexed by a **protocol**; the protocol generalises Essence's `T` |

### 3.3 The single structural point

**An escape is part of the *answer*, not a *step*.**

- As a **state** (RubyCore today): an in-flight jump is something the machine is *doing*,
  so the enclosing continuation reacts by **stepping** — the context is consumed, law 3
  fails, and `val_stuck` forbids calling it a value. §2.4's obstructions are this fact.
- As an **answer** (everyone above): an escape is something a sub-computation *returned*,
  and the context consumes it by **case analysis**. No step, no disturbance, composition
  total.

---

## 4. What RubyCore already has, and the one line where it diverges

Three quarters of the design is in place:

1. **The state form, faithfully.** [`04-blocks-procs-control-flow.md`](04-blocks-procs-control-flow.md)
   §4 already writes `⟨…⟩^return(v,tgt) | ^break(v,tgt) | ^next(v) | ^redo | ^retry |
   ^exc(v)` — Essence's packed value with the tag split into kind + target. `Ctl.jump`
   implements it.
2. **Generativity, as `FrameId`s** — `lean-model-sketch.md` §1.1's adoption, and it is the
   better substrate (§5).
3. **The answer form at the run level**: `RunResult = .value | .uncaught | .unsupported |
   .outOfFuel | .stuck` is CakeML's `Rval | Rerr`, already.

And then `Evals` projects `.value`. Everything in §2 follows from that one line.

---

## 5. What this does **not** contradict

`lean-model-sketch.md` §"What we reject from Essence" rejected two things, and **both
rejections stand**:

- **Big-step** — rejected for effect order, `ensure`-during-unwind, divergence, and the
  bounded/concolic checking the user stories need. Nothing here asks for big-step. The
  mechanised form of the answer type is CakeML's *fuel-indexed functional* big-step, which
  is what `Interp.run` **already is**.
- **Generative exceptions as the mechanism** — "right concept, wrong substrate"; `FrameId`s
  give generativity without a meta-exception layer. Still right, and §2.5's census depends
  on it (the `unwind` arms are the frame-search).

Neither rejection touches the **answer type**, which is orthogonal to both axes. The
projection in `Evals` was a separate decision taken later, in `Denote/Sem/State.lean`,
with its own recorded rationale ("partial correctness … ruling out the type-stuck outcomes
is a different theorem on a different axis"). That rationale is exactly what §2.1–§2.3
measured the cost of.

---

## 6. The proposal, and its price

Answer-type the semantic reading:

```lean
inductive Answer
  | val (v : Value)        -- the run returned
  | esc (j : Jump)         -- the run escaped, and this is the escape
  | gate (reason : String) -- `.unsupported` — outside the modelled fragment

def EvalsA (m : Machine) (e : Expr) (a : Answer) (m' : Machine) : Prop := …
```

Then, concretely:

- **`SafeKont K` becomes indexed by `Answer`.** The escape case is a *clause* rather than
  a missing hypothesis, and it can carry `StateOk` — which is precisely what made
  `JumpStuckFree` false (§2.3).
- **The decomposition becomes total case analysis**, rather than one lemma per axis with a
  per-continuation side condition.
- **`CatchFree`/`JumpOpaque` stop being ad hoc.** They become the statement of *which tags
  a continuation intercepts* — Essence's `handle t`, Hazel's protocol in its simplest form.
- **Stuck-freedom and value typing stop being two ladders.** `¬ typeStuck` is a property of
  the `esc` arm; `denM τ` is a property of the `val` arm. One obligation, two clauses.

**The price, stated plainly.** Every one of the 83 obligations changes shape, and the 48
discharged ones each gain a case. For the nine leaf reads that case is trivial (a literal
cannot escape) and for the four `.const` rules nearly so; for the call family and the
declaration family it is real work. This is a re-statement of the judgment layer, not a
patch — it should be costed against the alternative, which is a second 83-rung ladder plus
a context-carrying `SafeKont` anyway (§2.3 says the naive version is false).

---

## 7. What it does not buy

- **Not Iris's `wp_bind`.** `Language.Context` is a statement about the *machine's* step
  relation, which genuinely does disturb contexts; `ctx_law3_fails_raise` stands whatever
  the judgment layer does. Answer-typing is CakeML's shape over the fuel interpreter you
  have, not a repair of the Iris instance. The Iris seat remains useful for what J36 built
  it for — adequacy.
- **Not divergence for free.** It is already free: `typeStuck .outOfFuel = false`, and
  safety properties are prefix-closed, so `∀ fuel` catches every real stuck outcome
  without needing termination. `while true; end` types `NilClass` in both `validate` and
  `srb`, and runs to `out of fuel` in the model [V].
- **Not reachability.** `while true; end; 1 + "s"` is genuinely safe and `validate` says
  `false`; `srb` gets it right via **7006**, a code `difftest/checker_relation.py`
  deliberately excludes as "a reachability opinion, not a type one" [V].

---

## 8. Open questions

- **[?]** Does `Answer` need the *target* as well as the jump (`retJ v tgt`), or is the
  `Jump` payload enough? §2.3's `nxtJ` re-entry suggests the target matters at a back edge.
- **[?]** Can the `gate` arm be collapsed into `esc`? They behave alike for stuck-freedom
  and differently for coverage reporting.
- **[?]** How much of the 48 survives mechanically? The obligations are *derived* from
  `Judge`'s constructors (`Denote/Sem/Obligations.lean`), so the restatement is one edit to
  the derivation — but the proofs are not derived, and that is where the cost is.
- **[?]** Does the same restatement fix `lean/`'s `KontOk` cost, or is it orthogonal?
  `lean/` types the continuation syntactically, one constructor per frame; an answer-typed
  `SafeKont` would need none.

---

## 9. Sources

Read in full this session: Ueno, Fukasawa, Morihata & Ohori, *The Essence of Ruby*, APLAS
2014 (`ruby_papers/essence_of_ruby.pdf`) — §2 motivation, §3.2 control calculus, Fig. 2
evaluation rules.

Cited from the literature **[D]**, not re-read here: Guha, Saftoiu & Krishnamurthi, *The
Essence of JavaScript*, ECOOP 2010; Wright & Felleisen, *A Syntactic Approach to Type
Soundness*, 1994; Owens, Myreen, Kumar & Tan, *Functional Big-Step Semantics*, ESOP 2016;
Moggi, *Notions of Computation and Monads*; Plotkin & Pretnar, algebraic effects;
Thielecke, double-barrelled CPS; de Vilhena & Pottier, *A Separation Logic for Effect
Handlers*, POPL 2021.

Mechanised here **[M]**: `ratchet/Denote/Rules/VasgnStuck.lean`,
`ratchet/Denote/Rules/WhileStuck.lean`, `ratchet/Denote/Rules/WhileStuck2.lean`,
`lean/RubyCore/HCtx/Bind.lean`. All axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`).

---

## 10. Built — the decomposition layer, and what it cost *(2026-09-11)*

§6 was implemented **for the decomposition layer only**, deliberately: that is where all four
of §2's walls actually stand, and it can be done without touching the 83 obligations or the
48 discharged rungs. Four files, all axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`), full `lake build` green, and **both ladders unmoved** — `semladder` 48/83,
`run_ratchet.sh` 178/254. Nothing existing was deleted; the old lemmas still build and are
still consumed by the 48.

| file | what it is |
|---|---|
| `ratchet/Denote/Sem/Answer.lean` | `Answer`, `answerPoint`, `runA`, `ARes.out`, and **`run_pushK`** |
| `ratchet/Denote/Sem/SafeKont.lean` | `SafeKont`/`Delivers`/`HaltBlind`, `safe_pushK{,_le}`, the fuel arithmetic, `delivers_safeA` |
| `ratchet/Denote/Sem/AnswerValue.lean` | `run_split_A` — `run_split` re-derived, to show the value axis survives |
| `ratchet/Denote/Rules/VasgnAnswer.lean` | `SemStuckA.Judge.vasgn` — the control, same `Prop` as the old rung |
| `ratchet/Denote/Rules/WhileAnswer.lean` | **`SemStuckA.Judge.while'`** — §2.3's wall, gone |

### 10.1 The master equation **[M]**

```lean
theorem run_pushK (K : List Kont) (hK : RubyCore.Proof.CatchFree K) :
    ∀ fuel m, Interp.run fuel (pushK K m) = (runA fuel m).out K
```

One equation, one hypothesis, five outcomes accounted for. `runA` is `Interp.run` stopped at
the **answer point** — an empty continuation with a value or a jump in flight — rather than
run through it, and `ARes.out` reassembles. The coincidence that makes the cut correct is
that the answer point is *exactly* `RubyCore.Proof.stepFn_frame`'s side condition
(`hside_of_none`, two lines): the states where appending a continuation changes what happens
next are the states where an answer is handed over.

`CatchFree` survives, as §7 predicted: it is a fact about `stepFn` (a `throw` reads the whole
continuation), not about the projection.

### 10.2 Cost, measured **[M]**

Non-blank, non-comment lines of the theorem body.

| | projection | answer | note |
|---|---|---|---|
| decomposition, value axis | `run_split` **82** | — | |
| decomposition, stuck axis | `stuckFreeRun_pushK_le` **86** | — | |
| decomposition, both axes | — | `run_pushK` **62** + `stepFn_frameR` **21** | one induction, not two |
| `run_split` recovered | — | `run_split_A` **41**, no induction | |
| jump side condition, value | `JumpOpaque` 3 + `jump_empty_never_value` **27** | *deleted* — one `exact` in `run_split_A`'s `esc` arm | |
| jump side condition, stuck | `JumpStuckFree` 4 + `jumpStuckFree_asgnK` **14** | `safeKont_asgnK_esc` **7** | |
| the `vasgn` rung | 16 | 12 | same `Prop`, checked by `example` |
| the `while'` rung | `loop_stuck_of_jumps` **41**, *two false hypotheses* | `loop_stuck` **65**, *no hypotheses* | proves both loop entry points |

Net: 168 lines of paired induction become 83, one of the two jump side conditions is deleted
outright and the other shrinks by half, and the `while'` rung grows by 24 lines in exchange
for being **true**.

### 10.3 §2.3's wall is gone **[M]**

`SemStuckA.Judge.while'` is `SemStuck.Judge.while_of_jumps` minus `hJc`/`hJb` — the two
`JumpStuckFree` hypotheses §2.3 refuted — and plus one premise that is satisfiable:

```lean
def AnswerOkAt (κ : Ctx) (Γ : Env) (I : Ty) (e : Ratchet.Expr) : Prop :=
  ∀ m, StateOk κ Γ I m → Delivers (evalFrom m e) (fun _ m₀ => StateOk κ Γ I m₀)
```

`Delivers` quantifies over **answers**, so this one definition says both "the loop re-enters
conformant after a normal iteration" (the `val` arm — what `WhileStuck2.lean` took from
`SemJudge`'s third conjunct) and "…and after a `next` or a `redo`" (the `esc` arm, which no
obligation of `SemJudge`'s shape can state, §2.1).

Non-vacuity, which `WhileStuck2.lean` could not exhibit at all: `StuckFreeAt κ Γ I (.while'
(.int 1) (.int 2))` is proved with every hypothesis discharged, from `answerOk_pure` (a
two-line leaf lemma) and the existing `stuckFree_pure`.

**And `AnswerOkAt` is not a new invention — it is the meaning of a premise `Judge.while'`
already carries.** §F23 added `nxtPrefixOk body = true` ("a `next` may only occur before
anything has assigned") after a reachable soundness bug found by *reading* this rule's
semantic obligation; its whole purpose is to make the environment at a mid-body `next` equal
the body's incoming one. That is `AnswerOkAt`'s `esc` arm, verbatim. So the answer type does
not merely make the loop provable — it gives §F23's premise the first obligation that can
consume it, which is precisely §2.1's complaint about `raise`'s `excName?`.

### 10.4 Two of §8's open questions, closed **[✗→]**

- **Q1 — "does `Answer` need the target as well as the jump?"** **No.** `Jump` already
  carries what a target-sensitive arm needs (`retJ v tgt`), and the back edge turned out not
  to want the target at all: `whileUnwind`'s `nxtJ`/`redoJ` arms re-enter at `m₀`, and what
  they need is `StateOk κ Γ I m₀` — a fact about the *machine*, supplied by the `esc` clause.
  §2.3's suggestion that "the target matters at a back edge" was reading the right symptom
  and naming the wrong cause.
- **Q2 — "can the `gate` arm be collapsed into `esc`?"** **The question was malformed, and
  §6's three-armed `Answer` was wrong.** `.unsupported` is never *delivered* to a
  continuation; it aborts the run regardless of what is below it. So it belongs with
  `.uncaught` and `.stuck` in a separate `Halt`, and `Answer` has exactly two arms.
  The distinction that matters is **delivered vs. terminal**, not value vs. escape vs. gate.
  `HaltBlind` is the residue: the one thing a composition must know about a halt is that the
  property being proved does not read the continuation off its reported machine, which is
  two lines to discharge and is bookkeeping for `Interp.run`'s habit of reporting the
  *pre-step* machine on `.unsupported`/`.stuck`.

### 10.5 What was **not** done, and why

- **`SemJudge` is not restated.** §6's price — "every one of the 83 obligations changes
  shape, and the 48 discharged ones each gain a case" — is not paid, and on this evidence
  need not be paid to get most of the benefit: `run_split_A` shows the existing obligations
  consume the new decomposition **unchanged**. The restatement is worth doing when a rung
  needs to *conclude* something about an escape, and the first such rung is not on the value
  ladder at all — it is the second ladder's `while'`, which is now proved without it.
- **The second ladder is still two rungs long** (`vasgn`, `while'`, plus `intLit`). This
  session removed the wall in front of it; climbing it is a separate, and now unblocked,
  exercise.
- **§2.4 stands untouched**, exactly as §7 said it would. Nothing here repairs the Iris
  `Language.Context` instance and nothing here needs to.
- **§8's Q3 and Q4 are still open**, and Q3 ("how much of the 48 survives mechanically?") is
  now answerable cheaply, since the decomposition it depends on is a corollary rather than a
  rewrite.
