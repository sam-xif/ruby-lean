# RubyCore Semantics — Co-Semantics of Ruby and Rails

> **Status:** early design artifact, expected to grow. This sketches a *framing and a
> methodology*, not yet a rule set — the concrete abstract rules land alongside the Rails
> vertical slice (future artifact 10). Evidence tags as elsewhere: **[V]** verified
> against CRuby 4.0.5, **[D]** from docs, **[?]** open question to pin during
> mechanization / differential testing.
>
> Notation: `00-notation-and-syntax.md`. Object/heap model: `01-object-model.md`.
> Dispatch: `02-dispatch-and-mro.md`. Differential testing & `obs`:
> `05-differential-testing.md`. This artifact reuses all four; it introduces no new
> evaluation rules for the *core*.

This document proposes a **co-semantics** of the Ruby language and the Ruby on Rails
framework: not "Ruby semantics plus extra rules for Rails," but a **pair of semantics at
two altitudes joined by a correspondence theorem**. It explains why that pairing is the
right shape, how it snaps onto the existing artifacts (especially the "metaprogramming is
heap mutation" bet of artifact 02 §6), and what concretely to build — much of it testable
today under CRuby alone, before the Lean interpreter exists.

---

## 1. The tension this resolves

The project takes a deliberately deflationary stance on Rails (artifact 02 §6,
PROJECT_PLAN §5.3):

> Rails adds **no new evaluation rules**. `belongs_to`, dynamic finders, `before_action`
> — all reduce to mutating `methods` / `ancestors` / `eigen` in the heap, after which
> ordinary dispatch (artifact 02 §3) applies.

Read literally this says Rails needs *no semantics of its own*: run the RubyCore model on
Rails source and you are done. That is true and it is unsatisfying, because it describes
Rails at the **wrong altitude**. When a developer writes

```ruby
class Post < ApplicationRecord
  has_many :comments
end
```

the meaning they reason about is *"instances gain a `comments` method returning the
associated `Comment` records, lazily loaded and memoized, invalidated on save"* — not
*"the class's method table acquired several entries during `class_eval`."* Both
descriptions are true. They are one system viewed at two levels.

**A co-semantics is precisely the machine for relating those two levels.** It is the only
framing under which the "co-" earns its keep, and it delivers something the current
Phase-5 plan — Rails as a mere differential-testing *target* (artifact 05 §4 item 4) —
does not: an *explanation* of Rails idioms in their own terms, provably backed by the
core.

---

## 2. Three readings of "co-semantics" (compatible, not rival)

### 2.1 Stratified / refinement — the structural reading

Two machines:

- **Low level** — the existing `Step` over RubyCore configs `⟨K,H,Ξ⟩` (artifacts 00–04).
- **High level** — a `Step_Rails` over *domain* states: a routing table, a set of model
  classes with their associations, a callback chain, a request/response in flight.

A **refinement** connects them: an abstraction map `α : H → A` (concrete heap → abstract
Rails state) — dually a concretization `γ`, à la abstract interpretation — such that every
abstract step is *realized by* a run of concrete heap mutations, and the concrete heap
viewed through `α` *is* the abstract state. The correctness statement is a **simulation
square**:

```
   abstract:   A  ──── Step_Rails ────▶  A'
                │                          │
                α (or γ⁻¹)                 α
                │                          │
   concrete:   H  ──── Step* ───────────▶ H'
```

This is the verified-compiler shape (CompCert-style), pointed *upward*: it turns "Rails
is just heap mutation" from a dismissal into a **theorem** — `has_many` is *correct* iff
the heap it produces refines the abstract association it denotes.

### 2.2 Coalgebraic / coinductive — the "co-" reading (the deep one)

"Co-" in the mathematical sense. A Ruby object with mutable ivars and message dispatch
*is a coalgebra*: a state together with a transition `state → (message → state ×
response)`. This is not an analogy — it is exactly artifact 02's `send`. The natural
equivalence on coalgebras is **bisimulation**: two objects are indistinguishable iff no
sequence of message sends tells them apart.

That connects straight back to the harness: the observation function `obs⁺` (artifact 05
§3) is a **finite, empirical approximation of bisimilarity**. Differential testing
already asks *"does any observation distinguish the model from CRuby?"* — a bisimulation
game played against a bounded opponent (bounded corpus, bounded depth).

Rails is where coinduction stops being decorative, because Rails is saturated with
genuinely *ongoing / observational* behavior that least-fixed-point (inductive) semantics
models awkwardly:

- the request → response lifecycle (a stream of interactions, not one terminating value);
- `ActiveRecord::Relation` — lazy, chainable, forced only by observation;
- callback chains (`before_action` / `around_action`) as coinductively-composed processes;
- memoized associations invalidated by state change.

Modeling these as coalgebras yields the *right* equivalence for free: "this refactored
controller behaves the same" = **bisimilar under the request-message interface**.

### 2.3 Co-evolutionary — the methodological reading

Develop the two semantics *together*, each disciplining the other. Rails' real demands
decide which corners of Ruby must be faithful — exactly PROJECT_PLAN's "80% of the value
in a *specific* 20%": `method_missing`, `class_eval`, the `included`/`inherited` hooks,
`const_missing`. Conversely the Ruby model bounds which Rails behaviors are even
expressible. This is less a mathematical object than a *project discipline*, but it is
what keeps the effort honest and blocks the "model all of Rails" trap (PROJECT_PLAN §9).

### 2.4 How they fit together

Readings 1 and 2 are not alternatives — **2 rescues 1's central failure mode.** The
structural abstraction `α` (read associations back out of the method table) breaks
exactly where Rails is most itself: a `method_missing`-driven dynamic finder never touches
the method table, so there is *nothing structural to abstract*. The coalgebraic reading
fixes this by abstracting via **observations (behavior), not heap structure** — see §7.
Reading 3 is the discipline under which we build 1 + 2. So the plan is: **synthesize 1 and
2, driven by 3.**

---

## 3. What we actually build

For each Rails idiom in the modeled slice, the co-semantics defines four things:

1. **An abstract signature** — the domain state the idiom touches and an abstract
   transition over it (an entry in `Step_Rails`).
2. **Its realization** — the exact heap mutation it compiles to. For several idioms this
   *already exists* in artifact 02 §6 (the `belongs_to`/`has_many`/dynamic-finder rows).
3. **The abstraction map `α`** — heap → abstract state (structural where possible;
   observational where not, §5).
4. **A correspondence obligation** — the commuting square of §2.1, which serves *two*
   masters at once:
   - a **proof goal** in Lean (a simulation lemma, discharged once the interpreter and
     `Step` relation exist — same adequacy machinery as claim C3, artifact 05 §1; the
     precise theorem shape — coupling invariant, stuttering, `escape` — is §5);
   - a **differential test** runnable *today* under CRuby alone — the metamorphic / C2
     lever (artifact 05 §4.2) lifted from desugarings up to Rails macros.

The most important consequence:

> **The correspondence obligations are testable now, without the Lean model, exactly like
> the desugar round-trip (artifact 06).**

`has_many :comments` and its hand-expanded `define_method` form should be
`obs⁺`-indistinguishable. That is a co-semantics claim checkable this week with the
existing harness — the round-trip idea carrying from desugarings up to framework macros.

---

## 4. Worked micro-example: `has_many`

- **Abstract state** `A` maps `Post ↦ { comments: HasMany(Comment, fk: :post_id) }`.
- **Abstract transition** `Step_Rails`: evaluating `has_many(:comments)` in the class body
  adds that entry. The denotation of `post.comments` is *"the set of `Comment` records
  whose `post_id == post.id`"*.
- **Realization** (artifact 02 §6): at `class_eval` time, insert the
  reader / writer / `comments=` / collection-proxy methods into `Post`'s method table —
  ordinary heap mutation, after which dispatch is ordinary.
- **`α`**: scan `Post`'s method table for the association-shaped method cluster and recover
  `HasMany(Comment, …)`. *(Structural — works here because `has_many` does define methods.
  Contrast the dynamic-finder case in §7.)*
- **Correspondence**: the square commutes ⇒ `post.comments` under the concrete heap yields
  exactly the abstract association's denotation. **Check by `obs⁺` today** (macro vs.
  hand-expansion); **prove in Lean** once the interpreter lands.

Further worked idioms (`before_action` callback chains as process composition; dynamic
finders via `method_missing`; ActiveSupport open-class core extensions) will be added as
the slice grows. `before_action` is the natural second example because it exercises the
*coinductive/process* reading (2.2) rather than the structural one.

---

## 5. Shape of the proof goal

The naive statement — *"given the concrete initial state obtained by loading the Rails
framework source, every state any Rails program can reach maps to an abstract Rails state
via a pair of observation functions"* — bundles four things the standard refinement
machinery deliberately separates. Pulled apart, the goal becomes provable. (This section
shares its vertical machinery — **stuttering forward simulation** — with the sibling
artifact `../../../relating-language-and-substrate.md`, so the Ruby↔Rails and Ruby↔POSIX
vertical claims can reuse the same Lean infrastructure.)

### 5.1 A coupling invariant replaces "reachable from the real initial state"

Quantifying over states reachable from a term containing real Rails (~400kLOC) is the
wrong *kind* of statement — reachability from a giant closed term is model-checker
territory, not a simulation proof. The standard move (CompCert, seL4) is an **inductive
coupling invariant** plus three theorems:

```lean
-- A *relation*, not a function (see §5.2)
Inv : Config → AbstractState → Prop      -- "the concrete heap is a well-formed
                                          --  realization of this abstract Rails state"

-- (A) Initialization establishes it — over miniRails, not real Rails (§5.4)
theorem init_ok :
  ∀ P, Boot (miniRails ++ P) ⇓ C₀ → Inv C₀ (abstractInit P)

-- (B) Steps preserve it — the §2.1 square, with stuttering
theorem step_sim :
  ∀ C A, Inv C A → Step C C' →
      (Inv C' A)                                   -- stutter: abstract side doesn't move
    ∨ (∃ A', Step_Rails A A' ∧ Inv C' A')          -- match: the square commutes

-- (C) Cash value: on quiescent states the two altitudes agree observationally
theorem obs_agree :
  ∀ C A, Inv C A → Terminal C → obs_H C = obs_R A
```

"All reachable states map to abstract states" falls out as a *corollary* by trace
induction — it is never the proof goal itself. The invariant is local and checkable per
rule; global reachability is not.

The **stuttering disjunct is not decoration**: mid-way through `has_many`'s `class_eval`
(three of seven methods inserted) the heap corresponds to *no* completed abstract
transition. One `Step_Rails` ≈ thousands of `Step`s; the square commutes only at **commit
points**. Weak/stuttering simulation is exactly the tool for that.

### 5.2 `Inv` is a relation, not a pair of observation functions

The "two observation functions" formulation is the functional special case
(`Inv C A ↔ obs_H C = obs_R A`). Keep the general relational form because:

- **`α` isn't functional on the concrete side** (§7): a `method_missing`-driven
  capability leaves nothing in the method table to project — its clause is behavioral,
  naturally a relation.
- **Mid-stutter states** must be `Inv`-related to the *pre*-transition abstract state,
  which a strict project-both-sides-and-compare equation rejects.

Observation functions instead supply the theorem's cash value via `obs_agree` — and
`obs⁺` (artifact 05 §3) is its finite empirical approximation, which is why
correspondences are differential-testable before any Lean exists.

### 5.3 The quantifier over "any Rails program" — the real landmine

`P` is arbitrary Ruby: it can `Router.class_eval { … }`, monkey-patch
`ActiveRecord::Base`, `remove_method` framework internals. For such `P` the theorem is
**false** — the concrete system escapes every abstract state. Two standard outs:

1. **Rely–guarantee / well-behaved client**: restrict `P` to a fragment touching
   framework state only through the modeled API surface (CompCertO-style interface
   conventions, transposed).
2. **Escape as an abstract event**: give `Step_Rails` an explicit `escape` transition;
   the first `Inv`-breaking concrete step maps to it, and the co-semantics honestly says
   "beyond here, drop to the core semantics."

We take **(2)**, with (1) as a lemma characterizing when `escape` is unreachable. (2)
keeps the theorem total over all programs — what an adversarial-robustness story needs —
and composes with the confinement/monitoring direction
(`../../../bounded-effect-checking.md`): an `escape` event *is* the semantic-diff alarm
("a metaprogramming backdoor is a heap delta").

### 5.4 Real Rails source never enters the proof

Split, per the project's standing trust architecture (prove about the model, test the
model against reality):

- **Proved (Lean):** `init_ok` / `step_sim` / `obs_agree` about **miniRails** — the
  artifact-10 vertical slice, a small term in *our own* semantics.
- **Tested (differential):** that real Rails booted under CRuby lands in heaps satisfying
  the observable projection of `Inv`, and that macro-vs-hand-expansion runs agree under
  `obs⁺`. Real Rails' 400kLOC touches the theorem only through this empirical layer.

**The full proof-goal package:** `Inv` (coupling relation) + `init_ok` (over miniRails) +
`step_sim` (stuttering, with `escape`) + `obs_agree` (adequacy corollary) — real-Rails
fidelity discharged by differential testing, not proof.

---

## 6. Everything hinges on `Inv` — its clause taxonomy and how to validate it early

That the whole edifice reduces to constructing `Inv` is not a weakness; it is the
standard economics of refinement proofs. The simulation theorems are *fixed machinery*;
**`Inv` is where 100% of the semantic content lives** (in seL4 the coupling invariant
famously dwarfed the simulation argument). Everything one would colloquially call "the
meaning of Rails" becomes clauses of `Inv`.

### 6.1 Clause taxonomy

`Inv C A` decomposes per-idiom — each clause is one §3 recipe row turned predicate:

| Kind | Shape | Cost |
|------|-------|------|
| **Structural** | "for each `(name ↦ HasMany(t, fk)) ∈ A.associations(k)`, class `k`'s method table has the reader/writer/proxy cluster with right-shaped bodies" | cheap — read off the heap |
| **Observational** | "for each probe `m` in `A`'s interface, sending `m` yields the response `A` prescribes" (the `method_missing` cases, §7) | expensive — quantifies over *executions*; each clause is a mini-adequacy lemma. Concrete reason to keep the probe set small. |
| **Frame / representation** | "the framework's own internals are unsmashed": router object has expected class, `ActiveRecord::Base`'s dispatch-relevant ancestors intact, no eigenclass surprises on framework objects | the unglamorous bulk (seL4 again); these are what the `escape` transition (§5.3) triggers on |
| **Commit-point structure** | `Inv` must hold *mid-stutter* (three of `has_many`'s seven methods inserted): either loosen `Inv` to tolerate partial clusters, or — cleaner — prove each macro body **atomic up to `Inv`** (no `Inv`-observing step interleaves; true in single-threaded Ruby unless the macro calls out) | a per-idiom design decision, recorded alongside the §3 entry |

### 6.2 `Inv` is empirically developable *now* (the strategic consequence)

The structural and frame clauses are just a **heap predicate**, and the harness already
projects heaps (artifact 05 §3.1). So, before any Lean:

1. Write `Inv` as an **executable Ruby predicate** over the live heap (reflection:
   method tables, `ancestors`, ivars).
2. Boot miniRails — or real Rails — run the vertical-slice scenarios, and **assert `Inv`
   at every quiescent point**.
3. Every counterexample is either a bug in the draft `Inv` (most, early on) or a genuine
   discovery about what Rails really does to the heap. Both are exactly the information
   needed before formalizing.

This is the same trust-building move as the desugar harness (artifact 06): validate the
definition against CRuby *before* it exists in Lean. The failure mode it prevents is the
expensive one — discovering mid-simulation-proof that the invariant was never true of
real Rails.

Note this reorders §10's priorities: the macro-vs-hand-expansion `obs⁺` test checks the
*square*; an executable-`Inv` checker checks the *coupling relation*. The second is
arguably the higher-value prototype, because `Inv` is the load-bearing artifact and the
hardest to get right.

---

## 7. The hard part, and why the coalgebra earns its place

`α` is not obviously a function, and that is the crux:

- **Many-to-one.** Different macros can produce heaps that abstract to the same state
  (`has_many` vs. a hand-rolled `define_method` cluster) — fine, `α` is allowed to forget.
- **No-structure-to-abstract.** A `method_missing`-driven dynamic finder
  (`Post.find_by_title(...)`, artifact 02 §3, rule SEND-MM) produces **no method-table
  entry at all**. A purely structural `α` sees nothing and cannot recover the abstract
  capability. **[?]**

The fix is reading 2.2: abstract via **observed behavior**, not heap structure. Define `α`
(or the correspondence itself) in terms of the *responses to a probing message set* — i.e.
bisimulation against an interface — so that "responds to `find_by_title` with the right
record" is captured whether the capability is realized by a defined method *or* by
`method_missing`. This is why the coalgebraic reading is load-bearing rather than
ornamental: it is the only `α` that survives Rails' most characteristic move.

Open threads here:

- **[?]** Exactly which probe set makes the observational `α` well-defined and stable under
  the §3.2 normalizers (object-id rewriting, hash-seed pinning).
- **[?]** Whether `α` should be partial (defined only on "well-formed Rails heaps") with a
  separate invariant, or total into an `Option`.

---

## 8. Fit with the existing plan

- **Extends Phase 5**, from "vertical slice as a test target" to "vertical slice *with its
  own semantics* and a refinement theorem back to the core." Strictly bigger claim, same
  corpus and same idioms (artifact 05 §4 item 4; future artifact 10).
- **Reuses the dual interpreter + relation design wholesale** (PROJECT_PLAN §5.1). The
  abstract level is just a second, much smaller `Step` relation; the correspondence is an
  adequacy-style theorem using the same machinery as C3 (artifact 05 §1).
- **Reuses `obs⁺`** as the empirical side of bisimulation (§2.2) and the **metamorphic /
  C2 lever** (artifact 05 §4.2) as the correspondence-test generator.
- **New formal objects are modest**: `Step_Rails`, the coupling relation `Inv` (§5–6),
  and one simulation lemma per idiom. No new *core* evaluation rules — consistent with the
  central bet (README "Central design bet").
- **Shares vertical machinery with the substrate investigation**: the stuttering forward
  simulation of §5.1 is the same shape as `../../../relating-language-and-substrate.md`'s
  "Piece 3," so the Lean infrastructure (weak simulation, commit points, escape/interface
  events) is built once.

---

## 9. Risks

- **`α` well-definedness** — the §7 problem. Mitigation: prefer the observational `α`;
  keep the modeled slice small so the probe set stays tractable.
- **`Inv`'s mass.** The frame/representation clauses (§6.1) are the bulk of the work and
  the least glamorous; underestimating them is the seL4 lesson. Mitigation: develop `Inv`
  executably against CRuby first (§6.2) so its true size is measured, not guessed.
- **Coinduction in Lean is real work** — well-founded vs. `partial` definitions,
  `Quot`-based bisimulation, productivity obligations for the request/relation streams.
  Mitigation: prototype one coinductive idiom (`ActiveRecord::Relation` laziness or a
  callback chain) small before committing the framing.
- **Scope creep** — the co-semantics must stay *slice-bound*: one abstract rule per modeled
  idiom, no more (PROJECT_PLAN §9 "model everything" trap).

---

## 10. Immediate next steps

1. **Highest-value prototype: the executable-`Inv` checker** (§6.2) — draft `Inv` for the
   `has_many` slice as a Ruby heap predicate, assert it at quiescent points of the
   vertical-slice scenarios under CRuby. `Inv` is the load-bearing artifact (§6) and the
   hardest to get right; measure its true size before formalizing.
2. **Cheapest concrete win:** a `has_many` (structural) and a `before_action`
   (process/coinductive) correspondence test in the existing harness — macro vs.
   hand-expansion, checked by `obs⁺`. Proves the round-trip idea carries from desugarings
   (artifact 06) up to Rails macros, *with no Lean model required*. (Checks the *square*;
   step 1 checks the *coupling relation*.)
3. Draft the observational `α` for the dynamic-finder case (§7) and settle the probe-set
   question **[?]**.
4. As the Rails slice (artifact 10) is authored, add one §3-shaped entry (signature /
   realization / `α` / correspondence) per idiom here, and cross-link — including its
   commit-point/atomicity decision (§6.1).

This artifact is intentionally a skeleton to expand: as idioms are modeled and
correspondences are tested or proved, they accrete into §4 (worked idioms) and the risks /
open `[?]` list contracts.
