# Dataflow tracing for concolic execution — emitting symbolic terms from the semantics

**Status: design only.** Nothing here is built. It specifies how the Lean model should
emit *dataflow* (not just control-flow) information so the concolic engine in
[`../../concolic/`](../../concolic/README.md) can build solver queries **without
re-deriving dataflow outside the semantics**.

Companions: [`../../../bounded-effect-checking.md`](../../../bounded-effect-checking.md) §2
(the engine shape), [`../../../type-safety-by-reachability.md`](../../../type-safety-by-reachability.md)
§3 (the application: finding type errors), and `../../concolic/implementation-notes.md`
K9–K10 (what is built today and the gap this closes).

Origin: a 2026-07-29 design conversation, prompted by the question *"why do we need to
traverse the AST at all — can't we just read the failed condition off the trace?"*

---

## 1. The requirement, stated precisely

The engine's inner loop needs, for each branch the program took, a **predicate over the
symbolic inputs** that is true exactly when that branch goes the way it went. Negating one
such predicate and solving yields the next input.

Today the Lean tracer (`lean/ConcolicMain.lean`) emits only the branch **direction**. That
is sufficient for control flow but not for constraint generation, because a condition is
generally *not* a syntactic function of the inputs. The minimal counterexample is in the
committed corpus (`concolic/programs/derived.rb`):

```ruby
n = __input__
x = n * 3 + 7
if x == 100 then nil.succ else 0 end
```

| What we have | Value |
|---|---|
| trace event | `{"kind":"if","taken":false}` |
| condition AST | `["send", ["var","local","x"], "==", [["int",100]], null]` |
| what z3 needs | `n*3 + 7 == 100` |

Neither artifact contains `x = n*3 + 7`. That fact is **dataflow**, and it exists only in
the execution. Recovering it is the *sole* reason `concolic/collector.py` walks the AST
today — not control flow (the trace supplies that), not dispatch, not outcomes, not
truthiness.

### Why it cannot be recovered from a concrete trace

A tempting alternative is to log every primitive operation's concrete operands and results
and stitch the graph together afterwards. This fails on **ambiguity**: if a `==` had
receiver `7`, nothing identifies *which* earlier `7` that was. Concrete values carry no
identity, so the dataflow graph is not reconstructible from concrete observations alone.
Provenance must be tracked *while* executing.

### What the current workaround costs

The AST walk is a second traversal that must stay aligned with the model's evaluation
order, scoping, and call structure. It is guarded (a `DESYNC` check truncates the path
condition rather than emitting constraints off a mis-aligned walk), and the guard is
tested, but the coupling is real and grows with every construct the model gains. That is
the last correctness-relevant duplication left after K9 removed the parallel interpreter.

## 2. Design constraints

Any acceptable design must hold these. They are the lessons of K9 and of the
`Unsupported`-gate discipline.

1. **The semantics stays the artifact of record.** `stepFn` is difftested against CRuby at
   0 disagreements; a tracing facility must not put that at risk. Strongly preferred: no
   changes to `stepFn` at all (as achieved for branch tracing, where decisions turned out
   to be observable at the configuration level).
2. **Incompleteness degrades to *frontier*, never to a wrong constraint.** A missing or
   unmodeled dataflow edge must yield "no term" (→ no constraint, reported loudly), not a
   plausible-but-wrong predicate. A wrong constraint makes the solver derive inputs that
   do not follow the intended path — silent incompleteness, the failure mode the
   three-valued discipline exists to prevent.
3. **Coverage should be inherited, not chased.** As the model grows toward full Ruby
   (the metaprogramming gates are temporary), the engine's reach must grow with it
   automatically.
4. **Self-checking where possible.** Concolic execution has a free oracle: the concrete
   run. Any symbolic shadow can be checked against it continuously (§5).
5. **No new trust.** The engine remains untrusted; witnesses are still confirmed by
   replay. This design is about *capability and coupling*, not about trust.

## 3. Design space

| | Approach | Dataflow comes from | `stepFn` touched? | Outside work remaining |
|---|---|---|---|---|
| **D0** | status quo | AST walk outside | no | full walk: scopes, call structure, order alignment |
| **D1** | log condition *expressions* + symbolic locals | outside, per-condition | no | evaluate one expression per branch |
| **D2** | **symbolic shadow machine, driven by configuration observation** | inside Lean | **no** | term → z3 translation only |
| **D3** | symbolic values in the machine proper | inside Lean | **yes, pervasively** | term → z3 translation only |

**D1** is a real reduction (no program-wide traversal, no scope bookkeeping, no desync
risk) but keeps an expression evaluator outside and breaks down as soon as a condition's
value flows through a method return — it would have to follow that call, i.e. drift back
toward D0.

**D3** is the textbook answer: give values provenance. In this codebase it is unattractive
in a specific way — `Value` is a bare inductive matched in hundreds of places across
`Interp.lean`/`Builtins.lean`, so adding a field or constructor breaks all of them and
edits the difftested artifact. It buys nothing over D2 except uniformity.

**D2** is the recommendation. It exploits the same property that made branch tracing free:
`stepFn` is deterministic and dispatches on `(ctl, kont-head)`, so an external driver can
tell *which rule is about to fire* from the pre-state alone, and can therefore maintain a
**parallel symbolic state** in lockstep — without the machine knowing.

## 4. The recommended design (D2)

### 4.1 Term language

A small, serializable term language in Lean. `opaque` is load-bearing: it is how
incompleteness is represented (constraint 2).

```lean
inductive SymTerm where
  | inp   (k : Nat)                  -- the k-th symbolic input
  | lit   (n : Int)
  | neg   (t : SymTerm)
  | add | sub | mul  (a b : SymTerm) -- linear + multiplication
  | lt | le | gt | ge | eq | ne (a b : SymTerm)
  | truthy (t : SymTerm)             -- Ruby truthiness of a value term
  | opaque                           -- NOT symbolically tracked
```

Deliberately excluded for now: `/`, `%`, `**` (Ruby's flooring `Integer#/` does not line up
cleanly with z3's `Int`; per K7 these stay `opaque` rather than risk a wrong constraint),
and everything string/collection-valued (§8).

### 4.2 Shadow state

```lean
structure SymState where
  ctl    : SymTerm                          -- term of the in-flight value
  kont   : List SymKont                     -- term-mirror of the kont stack
  locals : List (FrameId × String × SymTerm) -- shadow of the frame store's locals
  notes  : List String                      -- frontier events
```

`SymKont` mirrors *only what can carry values into arithmetic or conditions* — e.g. for
`argsK` the accumulated argument terms; for `seqK`/`frameK` nothing. Every kont the mirror
does not model contributes `opaque`, which is safe by construction (constraint 2). Keying
`locals` by `FrameId` (rather than by name alone) makes the block/closure case work
naturally, since the model's shared-scope locals are already frame-store addressed.

### 4.3 The shadow step

```lean
def symStep (m : Machine) (m' : Machine) (s : SymState) : SymState × Option BranchEvent
```

Determined by `m`'s `(ctl, kont-head)` — the same discrimination `stepFn` performs — with
`m'` available to read off concrete results. Representative rules:

| Pre-state | Shadow update |
|---|---|
| `eval (.int n)` | `ctl := lit n` |
| `eval (.var .lvar x)` | `ctl := locals[currentFrame][x]` (default `opaque`) |
| `value v`, `asgnK .lvar x` | `locals[currentFrame][x] := ctl` |
| `value v`, `argsK … acc rest …` | push `ctl` onto the mirrored `acc` |
| primitive send resolving to a known op | `ctl := op recvTerm argTerms` |
| `value v`, `ifK _ _` | emit `branch(truthy ctl, v.truthy)` |
| `value v`, `whileCondK _ _` | emit `branch(truthy ctl, v.truthy)` |
| method entry (frame pushed in `m'`) | bind param names in `m'`'s new frame to the mirrored arg terms |
| anything unmodeled | `ctl := opaque`, append a note |

Two details worth pinning:

- **Recognizing a primitive op** does not require re-implementing dispatch. From the
  pre-state we know the *method name* and the receiver/arg **values**; if the name is in
  the op map and the operands are integers, we form the term — and then §5 checks it.
- **Jumps/exceptions** unwind the mirrored kont stack in step with the machine's, because
  the mirror is popped whenever the observed `kont` shortens.

### 4.4 Trace format

```json
{ "branches": [ { "kind": "if", "taken": false,
                  "cond": ["eq", ["add", ["mul", ["inp", 0], ["lit", 3]], ["lit", 7]],
                                 ["lit", 100]] } ],
  "outcome":  { "kind": "typestuck", "class": "NoMethodError", "message": "…" },
  "frontier": [ "untracked op Integer#% at …" ] }
```

`"cond": null` means the condition was `opaque` — the engine records no constraint and
surfaces a frontier line. The outcome classification is unchanged from today.

### 4.5 Inputs stop being an AST rewrite

Today the engine substitutes `__input__` → `["int", n]` in the JSON before each run. With
D2 the driver takes the input vector as an argument (`rubycore-concolic --inputs 31,7`) and
resolves the `k`-th `__input__` site to the concrete value *with term* `inp k`. Benefits:
one input site ↔ one symbolic variable, multiple inputs fall out, and no AST rewriting is
needed anywhere (K4's substitution machinery retires).

### 4.6 What the engine becomes

`collector.py` disappears. The engine keeps: run via Lean → read `cond` terms → translate
term JSON to z3 (a ~30-line recursive function, the irreducible "what does `+` mean to the
solver" map) → flip, solve, queue. No AST, no scopes, no evaluation-order alignment, and
the `DESYNC` failure mode ceases to exist.

## 5. Self-checking: the shadow validates itself against the concrete run

This is the design's strongest property and it should be built in from the start.
Every `SymTerm` we assign to `ctl` is a claim about the concrete run: *evaluating the term
at the actual inputs must equal the machine's actual value.* So carry the concrete input
vector, and at each assignment check

```
eval SymTerm inputs  ==  the concrete value the machine just produced
```

Mismatch ⇒ the shadow is wrong (a mirroring bug, or an op that does not mean what we
assumed) ⇒ set `opaque`, append a frontier note, continue. Consequences:

- mirroring bugs degrade to *lost precision*, never to wrong constraints;
- the check runs on every difftest program for free, so the corpus doubles as a validation
  suite for the shadow;
- "shadow drifts as the model grows" — the main worry about D2 — is *detected
  automatically* rather than discovered as a bad witness later.

A cheap extra check at the boundary: each emitted `branch.cond`, evaluated at the inputs,
must agree with the recorded `taken`.

## 6. Validation plan

1. **Per-step self-consistency** (§5) — on by default, reported as frontier.
2. **Branch-agreement** — emitted conditions reproduce the observed directions.
3. **Regression** — the four committed programs plus `derived.rb` must yield identical
   witnesses and iteration counts to the D0 engine.
4. **Prediction accuracy** (the new metric) — when the engine flips a branch and solves for
   an input, the *predicted* direction should actually occur on the next run. Report it as
   a percentage; gaps mean lost precision (frontier), not unsoundness. Run it over
   difftest tier-1 generated programs to get a number that tracks the model's growth.
5. **Ratchet** — tier-0 `--sut lean` stays 722 agree / 0 disagree, since `stepFn` is
   untouched.

## 7. Staging

| Stage | Content | Removes |
|---|---|---|
| **S1** | `SymTerm`, `SymState` with `ctl` + `locals`, straight-line arithmetic, `if`/`while`, self-check, term emission | dataflow through assignments (`derived.rb` works) |
| **S2** | kont mirroring for sends/args; param binding at method entry | dataflow through calls (`nil_dispatch.rb` works) |
| **S3** | engine switched to terms; delete `collector.py`'s traversal; input vector replaces AST substitution | the AST walk, `DESYNC`, K4 machinery |
| **S4** | prediction-accuracy harness over tier-1 programs | the "is the shadow keeping up?" blind spot |

S1–S3 are the payload; each is independently verifiable against the existing witness
corpus, so the migration is incremental rather than a flag day.

## 8. Honest hard parts and open questions

1. **Maintenance coupling remains — it just moves.** The mirror needs a rule per kont it
   wants precision on. This is strictly better than D0 (the coupling now lives in Lean,
   next to the semantics, and is checked by §5), but it is not zero. Only D3 removes it,
   at the cost of editing the difftested artifact.
2. **Truthiness of non-boolean conditions.** Ruby branches on any value; `truthy t` needs
   to mean "`t` is neither `nil` nor `false`". For integer-valued terms that is trivially
   true, which is fine but yields a useless constraint — so the term language may need a
   value-shape notion (is-nil / is-false) before conditions like `if x` (rather than
   `if x < 5`) become flippable. **Open.**
3. **Division/modulo.** Left `opaque` (K7). Modeling them means committing to z3
   encodings of Ruby's flooring semantics; worth doing eventually, with differential tests
   against CRuby on the encoding itself.
4. **Strings and collections.** Out of scope here. When they arrive the solver question
   changes (cvc5's string theory; array/sequence encodings) and the term language grows a
   sort discipline.
5. **Symbolic dispatch is the real prize, and this is the enabler.** The type errors that
   matter are dispatch-dependent: *which class* a receiver has depends on the input. Once
   terms exist, the natural next step is a term for "the class of this receiver" and
   constraints of the form `classOf(recv) ∉ {classes defining m}` — i.e. solving directly
   for inputs that make a dispatch miss, rather than stumbling onto them via arithmetic
   guards. That is the mechanism `type-safety-by-reachability.md` §3 describes and §7
   ranks as the central difficulty; it is out of scope for S1–S4 but is the reason to build
   this layer at all.
6. **Cost per run.** The shadow doubles the per-step work of a traced run. Irrelevant at
   demo scale; a real budget question when concolic search runs over `ai4r`-sized programs
   (`bounded-effect-checking.md` §7's path-explosion concern dominates first).
