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
  /-- **Keyed by a receiver *port*, not by a bare class** — see §4.5 and §4.6.
      `(inst c, n) ∈ noMethod` means *nothing in `c`'s instance MRO provides `n`*;
      `(cls c, n)` is the same for the class object's singleton chain **and** the metaclass
      tail it falls through to. Subsumes four encodings that are separate today: `nameFree`,
      `mroGet? … = none`, `smroGet? … = none`, and `MissFree`'s `method_missing`. -/
  noMethod   : List (Port × String)     -- `Port := inst String | cls String`
  freeConsts : List String          -- no constant of this path is bound

structure Scope where               -- neither; lexical, rebound on entry, never reported out
  frame      : Option Frame
  selfTy     : Option Ty
  blockTy    : Option Ty
  closures   : ClosTable
  asms       : AsmTable             -- see §7.3: an assumption, not a guarantee

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

### 4.4 `Pos` **is** the footprint, and the asymmetry that proves it

The judgment should be **local**: a rule states the facts it *requires* and admits any ambient
context that contains at least those and stays `Coherent`. Then the frame rule of §4 is
**admissible rather than primitive** — no rule is added, weakening does the work — and it is
available for free because `PosOk`/`NegOk` are antitone (§2.1, §3).

**The evidence that this is the right reading is that half of it is already true.** Counting
`Ratchet/Judge.lean`'s table premises:

| kind | form | count | local? |
|---|---|---|---|
| positive | `mroGet? κ.classes n m = some (dc, d)`, `clsGet? … = some`, `asmGet? κ.asms m argTys = some ρ` | 10 | **yes, already** |
| negative | `nameFree κ n`, `mroGet? κ.classes n m = none`, `defDeclared? κ.defs n = none` | ~24 | **no — every one is a whole-table scan** |

Every positive premise is a **lookup**: "the table contains at least this fact". That is
exactly the local reading, and it needs no change. Every negative premise is a **miss**:
`nameFree` scans `κ.defs` and every entry of `κ.classes`; `= none` is a claim about the whole
table. A miss is a global assertion wearing a lookup's clothes, and it is only ever as true as
the table's *completeness*.

**That asymmetry is F20.** The buried `def` did not make a lookup wrong — it made a table
incomplete, and a `= none` premise cannot tell the difference. Give `Neg` its own existence and
a negative premise becomes `(c, n) ∈ κ.neg`, a lookup like the others; then **every** premise is
local, no premise depends on any table being complete, and the frame rule is admissible on both
sides.

**The frame rule's side condition, precisely.** Not just coherence:

```
Judge S (P, N) Γ I e τ (P', N') Γ' I'
  →  keys(R) # keys(P' \ P)          -- R is disjoint from what e *writes*
  →  Coherent (P ⊎ R, N')            -- and adding R does not contradict what survives in N
  →  Judge S (P ⊎ R, N) Γ I e τ (P' ⊎ R, N') Γ' I'
```

Two departures from separation logic's version, both in our favour and both worth stating:

* **Read and write footprints separate here.** SL's `{P} C {Q}` conflates them — `P` is both
  what `C` needs and what it may clobber — so `R` must avoid everything `C` reads. Our facts
  are keyed and immutable-per-key, so `R` may freely overlap the *read* footprint: extra facts
  about a class the rule merely looked up cannot invalidate the lookup. Only the **write**
  footprint `P' \ P` must be avoided, and it is empty for every rule except the five
  declarations.
* **Coherence is a genuine extra condition, and it is the inheritance one.** Framing in
  `class D < C` changes the *meaning* of an existing `(D, n) ∈ N`, because `D`'s ancestor chain
  grew. So the side condition is not vacuous — but it is decidable, and it is the same
  `Coherent` §4.5 already needs.

**Locality costs the checker nothing.** It is a property of the *judgment*, not a burden on
`validate`: `chk` goes on computing one ambient context and discharging premises by lookup,
exactly as it does today. What changes is which propositions a derivation is allowed to lean
on — and therefore which programs `chk` must refuse.

### 4.5 `Neg` is keyed by class, and that is what makes `method_missing` work

The obvious first cut of `Neg` is a flat set of names, and it is wrong for the same reason F20
is wrong — it answers the question only for one implicit receiver.

**What the machine does.** `dispatchMiss` (`RubyCore/Interp/Reflect.lean`) looks up
`methodOn m.heap (classOf m.heap recv) "method_missing"` — the **receiver's** class chain, not
the caller's — and then `enterUserMethod m recv "method_missing" mm` makes `recv` the new
frame's `self`. So the receiver *does* become `self`, but only **after** the decision to
dispatch there; the decision itself is keyed by the receiver's class.

**What the checker already needs.** `Judge.callMissing` fires on an explicit receiver of type
`.inst n Iself` and carries

```lean
mroGet? κ.classes n m = none          -- no ordinary method, so the fallback may fire
¬ ObjectMethod m                      -- …and Object does not provide it either
mroGet? κ.classes n "method_missing" = some (dc, d)
```

The first is a **negative fact about class `n`**, encoded — exactly as in §1.2 — as a *miss in
the positive table*. The third is a positive fact. The second is a negative fact about the boot
heap. Three encodings of two polarities, in one rule.

So `Neg` is a relation, not a set:

```
(c, n) ∈ noMethod   ≜   no class in c's ancestor chain provides n
```

and the three premises become one positive lookup plus one `Neg` membership. `MissFree` is the
same relation at `(selfClass, "method_missing")`; `nameFree κ "lambda"` is it at
`(Object, "lambda")`. The scope-flag reading of `noMissing` survives only as the *implicit-self*
special case, where the key comes from `κ.selfTy` — which is why it looked like scope.

**Two consequences that are not bookkeeping.**

* **The fact is MRO-closed, so `include`/`prepend`/reopening can invalidate it.** That is the
  shrinking discipline doing its job, and it is a strictly better account than today's, where a
  `mroGet?` miss is re-computed from a table that a later `include` silently changes.
* **`Coherent` gets richer.** It is not `names(P) ∩ N = ∅` but

  ```
  ∀ (c, n) ∈ N,  P's MRO for c does not provide n
  ```

  i.e. the disjointness of §4 is *modulo inheritance*. This is the one place the design gets
  harder rather than easier, and it should be pinned before implementation.

**And `ObjectMethod` is the boot seed.** The ~45-name list is exactly `Neg`'s complement at the
boot heap: every class provides those, so no `(c, n)` with `n ∈ objectMethodNames` may ever be
in `noMethod`. Its own docstring already says "completeness is the soundness condition" — which
is precisely the hazard of a negative fact carried as a table, and an argument for deriving the
seed from `Denote/Sanity.lean`'s measured boot heap rather than maintaining the list by hand.

### 4.6 The key is a **receiver port**, not a class — instances, class objects, and eigenclasses

`(class, name)` is not enough, because Ruby has more than one lookup relation and the checker
already implements two of them plus a coarse belt for a third.

**Two ports.** They are the two walks `Ratchet/Judge.lean` already has:

| port | chain | the walk | consumed by |
|---|---|---|---|
| `inst C` | `prepends(C) ++ [C] ++ includes(C) ++ chain(super C)` … | `mroList?`/`mroGet?` | `Judge.callMissing`'s `mroGet? … = none` |
| `cls C` | `C.smethods ++ C.extended` (reversed) `++ singChain(super C)` | `lookupUpS`/`smroGet?` | `Judge.clsToS`'s `smroGet? … = none` |

So `Neg` is keyed by a *port* — `inst C` or `cls C` — and the two are read by different rules
for different receiver types (`Ty.inst n` versus `Ty.clsOf n`).

**The ports are not independent, and the dependency is §F7.** `lookupUpS` stops when
`c.super? = none`. Ruby does not: once the eigenclass chain is exhausted, `C.foo` falls through
to `Class → Module → Object → Kernel → BasicObject` **as instance methods**. So a
`class Module; def to_s; …; end` binds ahead of the builtin for *every* class object, and
`smroGet?` cannot see it. `nameFree κ "to_s"` is today's coarse belt for exactly that hole.

Keyed `Neg` makes the belt precise, as an **entailment the seed must respect**:

```
(cls C, n) ∈ Neg   ⟺   singChain(C) declares no singleton n
                    ∧   (inst Class, n) ∈ Neg          -- the metaclass tail
```

where the second conjunct unfolds through `Class`/`Module`/`Object`/`Kernel`/`BasicObject`'s
*instance* methods. This is strictly better than what it replaces: today's belt goes false as
soon as **any** class anywhere declares `to_s`; the keyed version asks only about the metaclass
tail. It is also the mechanism behind §10.1's claim that the keying pays for the seeding —
`Version#to_s` is an instance method of `Version`, so it touches neither
`(inst Pathname, "to_s")` nor the metaclass tail.

**Object eigenclasses need no third port**, and the reason is already in the denotation.
`Denote/Val.lean`'s `isExactInst` requires

```lean
o < h.objs.size && (h.get o).eigen.isNone && (h.get o).klass == k
```

— so `Ty.inst C` denotes only objects whose class is exactly `C` **and which carry no
singleton class**. An object that acquires one *leaves the type*. A `(inst C, n)` fact
therefore applies to exactly the values `.inst C` denotes, with no extra clause and no
per-object identity: the discipline the keying needs is already enforced on the semantic side.
(§F12 is why — the `.inst` arm was is-a and was tightened to exact; this is a second thing that
fix bought.)

**But `def obj.m` still needs F20's treatment on the syntactic side.** Today `clsMember?`
returns `none` for a `.defs` whose receiver is not `self'`, so the enclosing class never enters
the table and nothing using it is typed — sound, but *by gating one syntactic position*, which
is precisely F20's shape. Under a whole-program seed the rule is uniform and
position-independent:

> any `.defs` with a non-`self'` receiver, and any `define_singleton_method`, anywhere in the
> program, removes `(inst C, n)` and `(cls C, n)` for **every** `C`.

Coarse, and necessarily so: `Ty.inst` carries no object identity, so there is no finer sound
answer available. It is also cheap — no corpus program does this outside a class body, where
the existing gate already refuses it.

**Immediates are ordinary `inst` keys.** `.int`/`.flt`/`.str`/`.sym`/`.bool`/`.nilT` are
`inst Integer`/`Float`/`String`/`Symbol`/`TrueClass`|`FalseClass`/`NilClass`, and `classOf`
answers a boot id for them without reading the heap, so they can never carry an eigenclass and
the `eigen.isNone` conjunct is free.

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
| **`Judge.callMissing`'s three premises** | become one positive lookup and one `Neg` membership (§4.5) |

And what it does not fix, so the ladder's remaining shape stays honest: the `Builtins` heap walk
(§5.4), `ConstScopeOk`/the cref (§7.2), jump-freeness and the 22 call rules, `PrimSig`'s ~200
rows, and the `DenAllAt` transport falsity behind `arrayLit`/`hashLit`.

---

## 7. Three fields, decided

### 7.1 `closures` — **the table is `Scope`; the footprint is re-keyed to it**
The table itself is whole-program and constant (`collectBlocks`), so it is *scope* by the §2
test: never rewritten, never reported. §5.3 additionally wants a per-evaluation capture
footprint, and §10.2 settles its shape: **key the footprint by `ClosTable` index, not by frame
id.** Then it is static program data like every other threaded fact, and the index→frame
mapping — the only genuinely run-indexed part — stays on the semantic side in `ClosuresOk`,
which is where a closure invariant belongs and is currently `True`.

### 7.2 `consts` and the cref
The seventeenth stall point (`ConstScopeOk`) is **not** fixed by threading. It needs `Ctx` to
record the **cref** and the `.const` rules to resolve at the recorded cref rather than at the
toplevel. That is a different change to the same structure — worth doing in the same edit
window, and worth *not* conflating with this one in the write-up.

### 7.3 `asms` — **settled: `Scope`**
Neither a positive fact about the heap nor a negative one: it is a **conditional assumption**,
and `AsmsOk` is a claim about runs. It grows like a positive fact but its meaning is an
obligation, not a guarantee, and `Ctx.inMethod` already keeps it across a body entry for a
reason that is about scope ("a recursive call made from inside a body must still find the
assumption discharging it"). **Decision: `Scope`**, revisited when `callDef` is attempted —
that rule is the only one that grows the table and the only one that discharges it, so it is
the only rule that can tell us we were wrong.

---

## 8. Migration

### 8.1 Order
1. **F20's narrow fix, which *is* the `Neg` seed** — whole-program and **keyed by class**
   (§10.1: the keying has to land with the seeding, not after it, or the six slice programs
   regress), for the negative uses only; `κ.defs` unchanged for the positive ones. No signature
   change. Closes a reachable soundness bug, is independently valuable, and produces §11's
   measurement. Corpus witnesses for all three F20 shapes.
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

## 10. The four questions, resolved

Resolved 2026-09-09 with judgement rather than by further measurement, except where a
measurement was cheap — those are marked.

### 10.1 `Neg` is a **materialized set, seeded whole-program, keyed by class, threaded but constant**

Not a predicate. Four reasons, in the order they decide it:

1. **Membership has to be one decidable `Bool`.** The ratchet's architecture rests on
   obligations a kernel can check; `chk` discharges every other premise by lookup and this one
   should be no different. A semantic predicate (`n ∉ declaredAnywhere p`) is a fine *meaning*
   and a bad *premise*.
2. **Seed it whole-program** (§2.2). That is what closes F20, and it has a consequence worth
   more than the fix: a *static* declaration never has to shrink `Neg`, because it was never in
   it. Almost all of the maintenance burden and almost all of the coherence churn disappear.
3. **The seed can be MRO-closed**, because `extendClasses` already reads superclasses,
   `include`, `prepend` and `extend` statically. So the whole static hierarchy is visible to
   one pre-pass, and §4.5's "`Coherent` modulo inheritance" is established **by construction at
   seed time** rather than re-checked per rule (§10.4).
4. **Thread it anyway.** Dynamic declaration — `define_method` with a computed name,
   `Class.new`, `send(:include, …)` — is exactly what a syntactic pre-pass cannot see, and
   threading is where those shrink it. For the fragment `validate` types today **nothing
   shrinks `Neg`**, so it is a constant, and the proofs should exploit that rather than carry a
   generality no rule uses.

**Measured: what the whole-program seed costs, and why the keying more than pays for it.**
Six corpus programs use a guarded name *before* declaring it — `226/227/229/230/231/232`, all
Homebrew slice, all the same shape: `spec.to_s` at line ~123 inside `def self.process_spec`,
and `def to_s` at line ~226. A *coarse* whole-program seed (today's `nameFree` asks "does **any**
class declare this name") would go false program-wide and refuse them.

Keyed `Neg` does not: the fact those rules need is `(Pathname, "to_s") ∈ Neg`, which
`Version#to_s` leaves untouched. So **the keying of §4.5 recovers more precision than the
seeding of §2.2 costs**, and the net is finer-grained than today. The two changes are
complementary and should land together; landing the seed without the keying would be a
regression.

*(All six are tier 18/19, currently 0/8 and 0/3, so nothing on the ladder moves either way
today — but they are rungs the slice work intends to climb, so the interaction was worth
measuring rather than assuming.)*

**One hazard noted and not demonstrated.** Today's reading is ordering-sensitive, and a method
body is typed where it is *defined* and run much later — so a declaration between the two is a
window where a guard typed `true` could be false at call time. I probed the sharpest shape I
could construct (`class C; end; def m; C.to_s; end; class C; def self.to_s; 42; end; end;
m + "x"`); `validate` refuses it, so there is **no witness** and this is recorded as a
suspicion, not a finding. Making the fact order-independent removes the question rather than
answering it, which is a further argument for the seed.

### 10.2 The capture footprint is a **parallel component**, not a `Pos` field

Same discipline, different invariant, and the invariant is what decides it:

* **`Coherent` is what ties `Pos` to `Neg`**, and a capture footprint participates in no
  coherence condition with `Neg` — closures do not declare methods. Folding it into `Pos` would
  make every coherence check range over facts that cannot violate it.
* **The key spaces are disjoint by construction** — class×name versus `ClosTable` index — so
  they can never collide in the frame rule, and keeping them apart means the disjointness check
  never compares incomparable keys.

They do share a *shape*: a monotone set, an antitone interpretation, a `weaken` lemma and an
admissible frame rule. **Factor that shape once** — a small interface with `Ok`, `weaken` and
`keys`, instantiated at `Pos`, `Neg` and the footprint — so the Lean side gets one lemma per
instance instead of three ad-hoc families. That is the whole engineering content of this
answer.

### 10.3 A derivation's footprint is **`W = P' \ P`**, and nothing else

The one set of declaration keys the rule *writes*. Three exclusions, each load-bearing:

* **Reads need no accounting.** §4.4: premises are lookups, facts are keyed and
  immutable-per-key, so framed facts may overlap what a rule merely read.
* **`Γ` and `I` are not in it.** Locals and the self-ivar spine are already threaded in their
  own indices (`Γ → Γ'`, `I → I'`); they are state, but not *context* state, and adding them
  here would double-count.
* **Captures are the other key space** (§10.2), with their own `W`.

`W` governs both frame rules at once — `keys(R_P) # W` for the positive side and `R_N # W` for
the negative, since a rule that declares `(c, n)` invalidates exactly `(c, n)` among framed
negative facts. And **`W = ∅` for every rule except the five declarations**, so the side
condition is discharged by `rfl` in 78 of 83 cases.

### 10.4 `Coherent` modulo inheritance is a **seed-time property**

Resolved by 10.1(3). The pre-pass sees the entire static hierarchy, so it can compute an
MRO-closed `Neg` that is coherent with the whole program's `Pos` by construction. Coherence
becomes a per-rule obligation only for a rule that changes the hierarchy *dynamically*, and
`Judge` has no such rule today — `Class.new` and `send(:include, …)` are not typed. When one is
added it inherits the obligation, which is the right place for it.

## 11. What is genuinely still open

Both are **measurements, not designs** — they cannot be settled by thinking harder, only by
building step 1 of §8 and reading the number.

1. **Does keyed-and-seeded `Neg` hold `run_ratchet.sh` at 178/254?** §10.1 argues the keying
   pays for the seeding, and the six measured programs support it, but that is an argument
   about six programs and the corpus has 254. The honest expectation is that the number moves
   *up* (keying is finer than `nameFree`'s any-class coarseness) and that some rung shifts
   in each direction; whatever happens is the deliverable and should be recorded, not avoided.
2. **If the keying does not pay, does `Neg` need an ordered component as well?** The fallback
   is to keep a "declared already" set alongside the whole-program one and let the positive
   rules read the first while the negative rules read the second. It doubles the bookkeeping and
   should not be built pre-emptively — but it is the escape hatch if (1) comes back badly, and
   it is worth knowing it exists before starting.
