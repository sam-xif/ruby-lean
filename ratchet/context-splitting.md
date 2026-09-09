# Splitting the context: positive facts, negative facts, and a frame rule

**Status:** design, not built. Written 2026-09-09 after L268 measured why `JudgeSeq.cons`
cannot be discharged and F20 showed the same defect is a *reachable soundness bug*, not just an
awkwardness. Nothing in `Ratchet/` or `Denote/` has been changed for it yet.

**One sentence.** `Ctx` conflates three things — facts that only ever *grow*, facts that only
ever *shrink*, and lexical scope that does neither — and threads none of them out of a
judgment; splitting them by polarity makes every transport the ladder needs monotone in the
direction it needs, closes a soundness hole, and gives the closure/seal layer a *local* premise
where it currently has a `∀`-over-the-whole-heap.

---

## 1. The problem, in three pieces of evidence

This is not a tidiness argument. Three independent measurements point at the same defect.

### 1.1 `StateOk` transports in neither direction (L268)

`Obl.JudgeSeq.cons`'s second premise is at `κ.afterStmt e σ` and its conclusion at `κ`, so the
rung needs `StateOk` moved **both ways** across `afterStmt`. Both fail, and — this is the
useful part — they fail on *different components*:

| a bigger table makes the claim… | components | transport it gives |
|---|---|---|
| **weaker** — the antecedent fires on fewer names | `NameFreeOk`, `BareNameFree`, `MissFree` | up only |
| **stronger** — `∀ c ∈ C` ranges over more | `ClassesOk`, `DefsOk`, the `consts`/`privConsts` family | down only |

So `StateOk` is a conjunction of two families with **opposite variance in the same index**.
That is not a proof obligation that needs work; it is a sign that two different things are
sharing a field. Split them and each family is monotone in its own direction — and, as §3
shows, each direction is the one its consumer needs.

### 1.2 F20: the conflation is a reachable soundness bug

`found-issues.md` §F20. `Judge.defStmt` has no premise and types a `def` **anywhere an
expression is legal**; `extendDefs` — reached only through `Ctx.afterStmt`, which
`JudgeSeq.cons` applies to a *statement* — matches only a top-level `.def'`. So:

```ruby
x = (def lambda; 5; end)          # also: `if true; def lambda; 5; end; end`
f = lambda { 1 }                  # also: `[def lambda; 5; end]`
f.call + 1
```

CRuby and the Lean model both raise `NoMethodError`; `validate` returns `true` at `Integer`.
The guard that should have refused it is `nameFree κ "lambda"`, which asks **"is this name
*absent* from the positive table?"** — a negative fact encoded as the complement of a positive
one. That encoding is wrong for the same reason the variance table above is: absence is not the
complement of what one particular reconstruction happened to record.

### 1.3 The codebase has already worked around it twice

Both worked around *in `Ratchet/`*, with the reason written down at the time:

* **`capStaleCtx`** (`Ratchet/Judge.lean`) — "`Ctx` is an **input** to every rule: no rule
  rewrites it, so no rule can widen them. So they become a *premise* instead." That is the
  absence of `κ'` named explicitly, and paid for with a conservative premise on three fields.
  Its own docstring then names the alternative: "a `StateOk` component stating frame-chain
  disjointness — a bigger change… recorded in `found-issues.md` §F1 rather than built."
* **`Ctx.inMethod`** — entering a method body rewrites `selfTy` and `frame` and *keeps*
  `classes`/`defs`/`asms`. The scope/declaration split proposed below is already latent here;
  it simply has no name and no type.

And the design principle is already stated, for the *other* two pieces of state
(`Denote/Sem/Judge.lean`, choice 3):

> **The outgoing state is a conclusion, not a hypothesis.** `Judge` threads `Γ → Γ'` and
> `I → I'` as *outputs*… This is what makes the rules compose.

`κ`'s tables are state by exactly that test — `Ctx.afterStmt` is literally their update
function, applied in program order. They are the one piece of state left as input-only, and
`afterStmt` is the workaround: because a sub-derivation cannot *report* what it declared, the
sequence rule has to *reconstruct* it from statement syntax. F20 is what reconstruction misses.

---

## 2. The design

`Ctx` becomes three parts with three different disciplines.

```lean
structure Pos where                 -- grows along program order
  classes    : CTable
  defs       : DefTable
  consts     : Env
  privConsts : List String

structure Neg where                 -- shrinks along program order
  freeNames  : List String          -- no method of this name is declared anywhere reachable
  freeConsts : List String          -- no constant of this path is bound
  noMissing  : Bool                 -- no user `method_missing` is reachable from self

structure Scope where               -- neither; lexical, rebound on entry, never reported out
  frame      : Option Frame
  selfTy     : Option Ty
  blockTy    : Option Ty
  closures   : ClosTable
  asms       : AsmTable             -- see §7.3; assumption, not guarantee

structure Ctx where
  pos : Pos
  neg : Neg
  scope : Scope
```

The judgment threads the first two and takes the third as an input:

```lean
Judge (scope : Scope) (κ : Pos × Neg) (Γ : Env) (I : Ty)
      (e : Expr) (τ : Ty) (κ' : Pos × Neg) (Γ' : Env) (I' : Ty)
```

— written here with `scope` first to make the asymmetry visible; the real signature can keep
one `Ctx` in and one `Ctx` out with `scope` pinned equal by a premise, whichever elaborates
better (see §8.2).

**Only `Pos` and `Neg` thread.** `Scope` must not: a method body is typed with a different
`selfTy` and `frame`, and if those threaded out, `Judge.defStmt` would have to project the
body's outgoing scope back and every call rule would have to un-thread `selfTy`. `Ctx.inMethod`
already draws this line; this names it.

### 2.1 What the two polarities mean semantically

```lean
def PosOk (P : Pos) (m : Machine) : Prop          -- ∀ fact ∈ P, the heap exhibits it
def NegOk (N : Neg) (m : Machine) : Prop          -- ∀ name ∈ N, the heap exhibits nothing
```

Both are `∀`-over-a-set, so both are **antitone in their own index**: a bigger set is a
stronger claim. That is the whole mechanism, and §3 is why it is enough.

### 2.2 Seeding `Neg`

`Neg` is **seeded by a whole-program pre-pass**, not built up. `Ctx.withBlocks`
(`Ratchet/Validate.lean`) is the existing precedent — `κ.closures` is already filled from
`collectBlocks p` over the entire program for exactly this reason.

`freeNames` starts as *every shadowable name that no `def`, `define_method`, class body or
singleton-method definition anywhere in the program mentions*. This is the direct fix for F20:
a buried `def lambda` excludes `"lambda"` at seed time, so `Judge.lambdaLit`'s guard fails
without any rule having to notice the burial.

The polarity of the mistake matters here and is worth stating: **forgetting to seed a name into
`Neg` is conservative** (a rule declines), while forgetting to *remove* one is unsound. A
whole-program seed puts the fragile step at one place that sees all the syntax, instead of at
every rule that might declare something.

`Neg` then only *shrinks* for declarations a syntactic pre-pass genuinely cannot see —
`define_method` with a computed name, `Class.new`, `instance_eval` — which is a much smaller
and more honest surface than "every `def` in the program".

---

## 3. Why the transports now go the right way

This is the payoff, and it is mechanical.

| what a rule needs | direction | why it holds |
|---|---|---|
| feed `κ₁` out of premise 1 into premise 2 | none — it *is* `κ₁` | threading, not transport |
| weaken an outgoing `P'` back to a smaller `P` | `P ⊆ P' → PosOk P' m → PosOk P m` | antitone, one line |
| weaken an outgoing `N'` to a smaller `N` | `N ⊆ N' → NegOk N' m → NegOk N m` | antitone, one line |

`P` grows and `N` shrinks, so along program order the available facts move *toward* what every
consumer needs, and the only lemma required in either family is "weaken to a subset". Compare
§1.1, where the single conflated table needed one direction for one half of `StateOk` and the
opposite direction for the other half, and got neither.

**`JudgeSeq.cons` closes.** Premise 1 outputs `κ₁`; premise 2 consumes `κ₁` and outputs `κ₂`;
the conclusion outputs `κ₂`. No transport at any step. The run half is already proved and
axiom-clean — `evals_seq_cons` (`Denote/Rules/SeqCons.lean`, L268) — so this is the whole
remaining content of that rung.

**The five declaration rules become statable.** `Judge.defStmt`'s obligation stops being an
impossible transport and becomes *"one `stepFn` step installs exactly the method `κ'` records"*
— a provable statement about one step. Same for `classStmt`, `moduleStmt`, `casgn`,
`cpathAsgn`. Statable is not proved, but they are currently not even expressible.

---

## 4. Where the disjointness actually is

The instinct that this is a separation structure is right, but it is worth being precise about
*which* conjunction is separating, because the obvious candidate is not.

**Not between same-polarity facts.** `PosOk` is `∀ f ∈ P, φ f`, so

```
PosOk (P₁ ∪ P₂) m  ↔  PosOk P₁ m ∧ PosOk P₂ m
```

holds with **no disjointness side condition at all**. Facts of one polarity just conjoin.

**The disjointness is between the polarities.** `Pos` and `Neg` are not independent: adding
"class `C` declares method `m`" to `P` *invalidates* "`m` is a free name" in `N`. So the design
carries a well-formedness invariant

```
Coherent (P, N)  :=  names(P) ∩ N.freeNames = ∅   (and likewise for constants)
```

and it is `Coherent` that makes the two families composable. **The frame rule is the statement
that a derivation's effect is confined to its footprint**, so a context extended by anything
disjoint from that footprint comes through untouched:

```
Judge S (P, N) Γ I e τ (P', N') Γ' I'
  →  footprint e # R
  →  Judge S (P ⊎ R, N) Γ I e τ (P' ⊎ R, N) Γ' I'
```

That is the useful reading, and it is what makes composition cheap: a sequence of statements
that declare disjoint names needs no interaction reasoning between them, and — more to the
point — a rule consuming a sub-derivation does not have to re-verify the parts of the context
the sub-derivation never mentioned.

**Joins are forced, and forced conservative.** With `κ` threaded, `Judge.if'` must combine two
branches' outgoing contexts, and the polarities settle it with no room for invention:

```
P_out = P₁ ∩ P₂        -- only what both branches guarantee
N_out = N₁ ∩ N₂        -- only what both still guarantee absent
```

Both are the **meet**. This is worth noticing because the eleventh stall point
(`Denote/Sem/notes.md`) is a stated falsity caused by a join that took a *union*: `joinT`'s
union arm synthesizes `x : .sameAs y .int` from two entries neither of which promised an
identity. A discipline in which every join is a meet in both components cannot produce that
class of bug, and the `if`-buried-`def` shape of F20 (`if true; def lambda; …; end`) is refused
by `N₁ ∩ N₂` for the right reason.

---

## 5. The seal, and what separation buys there

The hoped-for application is `Denote/Sem/Locals.lean`'s `Sealed`. It is real, and it is worth
being exact about its size.

### 5.1 The shape of the problem

`Sealed b m` has three clauses, and two of them are `∀`-over-the-whole-heap:

```lean
stack : ∀ fid ∈ m.stack,      … does not reach b
clos  : ∀ o cl, procClosure? m.heap (.ref o) = some cl → ∀ p, cl.captured = some p → … ≠ b
meth  : ∀ k n md, methodIn m.heap k n = some md → ∀ p, md.capturedFrame = some p → … ≠ b
```

That is exactly the non-local, re-check-everything shape separation logic exists to avoid.
Every rule that allocates a closure has to re-establish a global property of the heap, and
`StateOk`'s `ClosuresOk` component — the place a closure invariant would live — is currently
`True`.

### 5.2 The right separation is over **frames**, not over the heap

This is the load-bearing observation, and it is what makes the idea affordable.

A genuine separating conjunction over Ruby's *heap* is not available cheaply: there is no
ownership discipline, and a closure can be reached through an ivar, a constant, a global or an
argument, so "these two expressions touch disjoint heap" is false in general.

But `Sealed` does not talk about the heap. It talks about the **capture graph** — a relation on
frame ids — and that graph is well behaved in a way the object graph is not:

* `CaptureDown` (already proved, `Denote/Sem/Locals.lean`) says a frame captures only an
  **older** frame. So the capture graph is a DAG with a topological order given by frame id.
* Frame ids are allocated monotonically and never reused.
* Since L266 a closure's capture is an `Option`, so "captures nothing" is expressible, and
  since L267 the graph has exactly three writers (stack, closures, methods) with no fourth.

So footprints are **finite sets of frame ids**, disjointness is decidable, and the frame rule
is over a structure that is already proved acyclic.

### 5.3 What that changes concretely

Add to `Pos` (or, more likely, to a fourth component keyed to the run rather than the program —
see §9.1) a **capture footprint**: *"evaluating `e` allocates closures and installs methods
capturing at most the frames in `F`."* Then:

| today | with footprints |
|---|---|
| `Sealed.alloc`'s premise is a `∀` over the heap re-proved at every allocating rule | the premise is `b ∉ F`, decidable, and the frame rule carries the rest of the heap |
| `Judge.lambdaLit` re-establishes a global closure invariant | it reports `F = {current frame}` and nothing else |
| composing two sub-derivations re-checks the whole heap | disjoint footprints compose by §4's frame rule |

This is the sixteenth stall point's own prescription arriving with a mechanism: it asked for
"an **exactness** component in `MethodsExact`'s mould… plus a syntactic premise over that
table", and a footprint *is* that premise, made compositional.

### 5.4 What it does **not** buy — stated so it is not over-read

* **It does not eliminate the `Builtins` walk.** L267 proved the frame half of `BuiltinsSeal`
  and left exactly two hypotheses: `Builtins.run` installs no capturing closure and no
  capturing method. In footprint terms that is `footprint(Builtins.run …) = ∅` — a cleaner
  *statement*, and still a traversal of the same six hundred arms. Separation gives you
  composition, not the walk.
* **It does not make the analogy to separation logic exact.** There is no magic wand, no
  ownership transfer, no fractional permissions, and no frame-preserving update on the heap.
  What is on offer is a frame rule for a **monotone fact algebra over a finite decidable
  domain**. Calling it separation logic will make readers expect more than it delivers.
* **It does not touch the call layer.** The 22 call rules need jump-freeness and an account of
  the activation between a frame push and its pop. Footprints say nothing about that.

---

## 6. What this fixes

| | effect |
|---|---|
| **F20** | closed by §2.2's whole-program `Neg` seed, independently of threading |
| **`JudgeSeq.cons`** | discharged — §3 plus the already-proved `evals_seq_cons` |
| **`defStmt`, `classStmt`, `moduleStmt`, `casgn`, `cpathAsgn`** | become *statable*; each turns into a one-step claim |
| **eleventh stall point** (join invents an alias) | the class of bug is excluded by "every join is a meet" |
| **`capStaleCtx`'s conservative premise** | can be replaced by a real outgoing context, recovering the precision §F1 records as lost |
| **the seal layer** | a local, decidable premise replaces a `∀`-over-heap; `ClosuresOk` gets its content |

And what it does not fix, so the ladder's remaining shape stays honest: the `Builtins` heap walk
(§5.4), `ConstScopeOk`/the cref (§7.2), jump-freeness and the 22 call rules, `PrimSig`'s ~200
rows, and the `DenAllAt` transport falsity behind `arrayLit`/`hashLit`.

---

## 7. Three fields that need a decision

### 7.1 `closures`
Currently whole-program and constant (`collectBlocks`). It is *scope* by the §2 test (never
rewritten, never reported). But §5.3 wants a per-run footprint, which is threaded. **Proposal:**
keep the syntactic table in `Scope`, and put the footprint in a threaded component; they answer
different questions ("which block literals does the program contain" vs. "which frames has this
evaluation captured").

### 7.2 `consts` and the cref
The seventeenth stall point (`ConstScopeOk`) is **not** fixed by threading. It needs `Ctx` to
record the **cref** and the `.const` rules to resolve at the recorded cref rather than at the
toplevel. That is a different change to the same structure — worth doing in the same edit
window, and worth *not* conflating with this one in the write-up.

### 7.3 `asms`
Neither a positive fact about the heap nor a negative one: it is a **conditional assumption**,
and `AsmsOk` is a claim about runs. It grows like a positive fact but its meaning is an
obligation, not a guarantee. **Proposal:** keep it in `Scope` and revisit when `callDef` is
attempted, since `callDef` is the only rule that grows it and the only one that discharges it.

---

## 8. Migration

### 8.1 Order
1. **F20's narrow fix alone** — whole-program `Neg` seed for the negative uses, `κ.defs`
   unchanged for the positive ones. No signature change. Closes a reachable soundness bug and
   is independently valuable; corpus witnesses for all three shapes.
2. **Split `Ctx` into `Pos`/`Neg`/`Scope`** with `afterStmt` still doing the growth. Pure
   refactor; the ladders must not move.
3. **Thread `Pos`/`Neg`** through `Judge`, retire `afterStmt`, rewrite the joins as meets.
4. **`SemJudge`'s conclusion** moves to `κ'`; re-prove the 47 discharged rungs.
5. **`JudgeSeq.cons`** — the first new rung.
6. Footprints and the seal (§5), as its own piece.

### 8.2 Cost, honestly
The clink-60 census prices this as "a change to `Judge`'s signature, i.e. to all 178
derivations". That is probably an over-estimate: most rules have `κ' = κ`, and the derivations
in `Ratchet/Rungs.lean` are proof terms whose new index should be inferred. But the codebase's
own convention exists because this goes wrong — `Judge.while'` carries `Γb = Γ` as an *equation
premise* precisely so "the elaborator resolves them from the sub-derivation rather than
unifying structurally in the wrong direction". Expect every threaded rule to need `κ' = κ` in
that same style, and budget for the elaboration to be the fiddly part rather than the proofs.

Touched: `Ratchet/Judge.lean`, `Ratchet/Validate.lean`, `Ratchet/Proof/ChkSound.lean`,
`Ratchet/Rungs.lean`, `CheckRungs.lean`, and every file under `Denote/Rules/`. Gates that must
hold throughout: `run_ratchet.sh` at 178/254, `run_check_rungs.sh` at 177/177 + 145/145 (both
will move at step 1, by the new corpus witnesses and by programs the fix now refuses — that
movement is the deliverable and should be recorded, not avoided), `semladder`'s denominator at
83, `Denote/Examples.lean` green, no `sorry`.

---

## 9. Rejected alternatives

**Strengthen `SemJudge`'s conclusion to `StateOk (κ.afterStmt e τ)` and leave `Judge` alone.**
The move the ladder's own instructions sanction, and it does not work: L268 measured that it
buys the *up* transport at the cost of the *down* one, leaving `JudgeSeq.cons`'s conclusion
unstatable. The variance table in §1.1 is the reason, and no lemma repairs it — the two
families need opposite directions in the same index.

**Make `SemJudgeSeq` conclude at the context after *all* of `es`.** Removes the need for a
downward transport by never going down. Blocked on a detail rather than a principle:
`extendConsts` takes the statement's **type**, and `SemJudgeSeq`'s signature carries only one
type for the whole sequence. Threading solves this by construction — each rule reports its own
type *and* its own context — which is an argument for threading rather than a competing design.

**Reach for iris-lean.** Real separation logic is already in this repo's dependency graph (the
H-layer, `judgment-layer.md` J36). Rejected for the checker: the facts here are decidable finite
sets, a bespoke lattice is far cheaper, and — decisively — the ratchet's architecture depends on
obligations being checkable by one kernel `Bool`. Introducing a program logic between `Judge`
and `stepFn` would put a second semantics in the trusted path for a structure that does not need
one. The H-layer remains the right home for genuine higher-order separation.

**Tighten `extendDefs` to scan buried declarations.** The obvious patch for F20 alone: make
`extendDefs` recurse into subexpressions the way `bodyConsts`/`bodyNested` already do for
constants. Rejected as the *primary* fix because it keeps absence encoded as the complement of a
reconstruction, so the next expression form that can contain a declaration reopens the hole —
and because it does nothing for the variance problem in §1.1. It is a reasonable belt-and-braces
addition alongside §2.2, not a substitute.

---

## 10. Open questions

1. **Is `Neg` a set of names or a predicate?** A list of names is decidable and cheap; a
   predicate (`n ∉ declaredAnywhere p`) is exact and needs no maintenance. The second is
   probably right for `freeNames` and wrong for `noMissing`.
2. **Do footprints belong in `Pos` or in a fourth component?** §7.1 argues fourth, because a
   footprint is about the *run* and `Pos` is about the *program*. Not settled.
3. **What is the frame rule's side condition, exactly?** §4 writes `footprint e # R`. Making
   that precise means deciding what a `Judge` derivation's footprint *is* — the names it
   declares, plus the frames it captures, plus (probably) the ivars it writes. Worth pinning
   before any of §8 step 3.
4. **Does `Neg` need per-scope entries?** `noMissing` is about `self`'s class, which changes on
   entering a method body — so it may be scope-relative, in which case some of `Neg` is not
   program-ordered at all and belongs with `Scope`. Check before implementing.
