# Dataflow tracing for concolic execution — emitting symbolic terms from the semantics

**Status: design; implementation in progress (S1).** Specifies how the Lean model emits
*dataflow* (not just control-flow) information so the concolic engine in
[`../../concolic/`](../../concolic/README.md) can build solver queries **without
re-deriving dataflow outside the semantics**.

Companions: [`../../../bounded-effect-checking.md`](../../../bounded-effect-checking.md) §2
(engine shape), [`../../../type-safety-by-reachability.md`](../../../type-safety-by-reachability.md)
§3 (the application), and `../../concolic/implementation-notes.md` K9–K11.

Origin: a 2026-07-29 design conversation (*"why traverse the AST at all — can't we read the
failed condition off the trace?"*), revised 2026-07-31 after a prior-art review (KLEE,
Rosette, Serval, K) and a proposal to emit SSA from the desugarer.

---

## 1. The requirement, stated precisely

The engine's inner loop needs, per branch taken, a **predicate over the symbolic inputs**
that is true exactly when that branch went the way it went. Negate one, solve, get the next
input.

The Lean tracer originally emitted only the branch **direction**. That suffices for control
flow but not for constraint generation, because a condition is generally *not* a syntactic
function of the inputs. The minimal counterexample is committed as
`concolic/programs/derived.rb`:

```ruby
n = $__in0
x = n * 3 + 7
if x == 100 then nil.succ else 0 end
```

| What we have | Value |
|---|---|
| trace event | `{"kind":"if","taken":false}` |
| condition AST | `["send", ["var","local","x"], "==", [["int",100]], null]` |
| what z3 needs | `n*3 + 7 == 100` |

Neither artifact contains `x = n*3 + 7`. That fact is **dataflow**; it exists only in the
execution. Recovering it is the *sole* reason `concolic/collector.py` walks the AST — not
control flow (the trace supplies that), not dispatch, not outcomes, not truthiness.

### Why it cannot be recovered from a concrete trace

Logging every primitive's concrete operands and results and stitching the graph afterwards
fails on **ambiguity**: if a `==` had receiver `7`, nothing identifies *which* earlier `7`
that was. Concrete values carry no identity, so provenance must be tracked *while*
executing. (KLEE's design is the same conclusion from the other direction — see §3.)

### What the current workaround costs

The AST walk is a second traversal that must stay aligned with the model's evaluation
order, scoping, and call structure. It is guarded (a `DESYNC` check truncates rather than
emitting constraints off a mis-aligned walk) and the guard is tested, but the coupling is
real and grows with every construct the model gains. It is the last correctness-relevant
duplication after K9 removed the parallel interpreter.

## 2. Design constraints

1. **The semantics stays the artifact of record.** `stepFn` is difftested at 0
   disagreements; tracing must not risk that. Strongly preferred: **no `stepFn` changes**
   (achieved for branch tracing, since decisions are observable at the configuration level).
2. **Incompleteness degrades to *frontier*, never to a wrong constraint.** A missing
   dataflow edge yields "no term" (→ no constraint, reported loudly), not a
   plausible-but-wrong predicate. A wrong constraint makes the solver derive inputs that do
   not follow the intended path — silent incompleteness.
3. **Coverage inherited, not chased.** As the model grows toward full Ruby, the engine's
   reach must grow automatically.
4. **Self-checking.** Concolic execution has a free oracle — the concrete run. Any symbolic
   shadow can be validated against it continuously (§6).
5. **No new trust.** The engine stays untrusted; witnesses are still confirmed by replay.

## 3. Prior art, and what it settles

| System | Value representation | Lesson for us |
|---|---|---|
| **KLEE** | every value is a `ref<Expr>`; **concrete is not a separate case** — a constant is a `ConstantExpr` leaf. Memory is theory-of-arrays (`Array`+`UpdateList`, read by `ReadExpr`), byte-granular, with a per-byte concrete fast path (`concreteStore`/`knownSymbolics`). | **No taint flag.** "Is this symbolic?" is structural: a value is concrete iff its term is a literal. Constant-fold at construction and fully-concrete computation collapses for free. Heap dataflow wants arrays, not renaming. |
| **Rosette** ([PLDI'14](https://dl.acm.org/doi/10.1145/2666356.2594340)) | lifts a **small core**; symbolic values of *unsolvable* types are **symbolic unions** (disjointly-guarded concrete values). `for/all` disassembles a union, applies unlifted code per component, reassembles. | Partial lifting with a principled escape hatch is validated. But note the correction below — this is *not* the same as our `opaque`. |
| **Serval** ([SOSP'19](https://dl.acm.org/doi/abs/10.1145/3341301.3359641)) | builds verifiers by **lifting interpreters** under symbolic evaluation (RISC-V, x86-32, LLVM, BPF). | The destination is sound and productive. Their headline contribution is **symbolic profiling** — the hard part was *blowup*, not soundness. Budget for that. Caveat: their targets are finite-width ISAs; Ruby is unbounded ints + strings + a growing heap + a mutable method table, so tractability does **not** transfer. |
| **K / KEVM** | one declarative rewrite semantics, **two backends** — LLVM (concrete) and Haskell (symbolic). | Even the flagship "semantics is everything" system keeps concrete and symbolic *evaluators* separate. See D4. |

**Correction worth recording:** an earlier note in this project equated our `opaque` with
Rosette's symbolic reflection. That is wrong, and the difference matters. Symbolic
reflection is **precision-preserving** — it replaces "can't handle this symbolically" with
a *finite case split over concrete possibilities*, runs real code per case, and merges,
keeping the full symbolic relationship as guarded cases. Our `opaque` is
**precision-losing**: it discards the term. Rosette's mechanism needs the value to be a
finite union of concrete possibilities — which is exactly what we will have for **dispatch**
after concrete boot (§9.5).

**Empirical settlement of the SSA question:** LLVM IR *is* SSA, and KLEE still maintains
dynamic `ref<Expr>` DAGs. So static SSA is neither necessary nor sufficient for symbolic
execution — see §5.

## 4. Design space

| | Approach | Dataflow from | `stepFn` touched? | Outside work |
|---|---|---|---|---|
| **D0** | status quo | AST walk outside | no | full walk: scopes, calls, order alignment |
| **D1** | log condition *expressions* + symbolic locals | outside, per-condition | no | an expression evaluator; breaks when a value flows through a return |
| **D2** | **shadow symbolic machine driven by configuration observation, emitting a φ-free trace-SSA dataflow log** | inside Lean | **no** | term → z3 translation only |
| **D3** | symbolic values in `Value` itself | inside Lean | **yes, pervasively** | term → z3 translation only |
| **D4** | one declarative `Step` relation, two evaluators (concrete + narrowing) | inside Lean | n/a (new evaluator) | solver call only |

**D3** is the textbook answer and the prior-art default — but every success above *designed
for it up front*. Ours would be a **retrofit** onto an interpreter difftested clean across
722 programs, with `Value` matched in hundreds of places in `Interp.lean`/`Builtins.lean`.
Prior art says the destination is sound; it does not say the retrofit is cheap.

**D4** is the north star: it dissolves the D2/D3 tension exactly as K does, and this project
already posits an inductive `Step` as the definition of record with `stepFn` as its
executable witness. A relation is declarative, so symbolic execution over it is narrowing.
Blocked on `Step` covering more than the control core, plus a narrowing engine — a project,
not a next step. **Recorded as direction, not plan.**

**D2 is the recommendation** and what §7 implements.

## 5. Rejected: emitting SSA from the desugarer

Proposed 2026-07-31: have `desugar` produce RubyCore already in SSA form, so dataflow is
explicit in the program rather than reconstructed. Rejected, for five reasons:

1. **It does not deliver what we need.** SSA names *static definition sites*; concolic
   execution needs *dynamic* value provenance. In a loop these diverge: `x₂ = φ(x₁, x₃)` is
   one static name for N dynamic values, and φ is not something a solver consumes. You
   would still build the per-iteration chain at runtime. KLEE-on-LLVM (§3) is the empirical
   proof.
2. **It addresses the least important part of Ruby's dataflow.** SSA renames *locals*;
   Ruby's state is mostly heap — ivars, array elements, hash entries. `@q[s][a] += …` is
   untouched. Heap dataflow needs theory-of-arrays (§8).
3. **Ruby's closures fight SSA.** Blocks capture locals by reference and mutate them (the
   model implements this with shared-scope locals over the frame store). Those are the moral
   equivalent of C's *address-taken* variables, which SSA construction **excludes** from
   promotion — so many interesting Ruby locals would be ineligible anyway.
4. **Blast radius.** RubyCore's shape is load-bearing for the desugar ratchet (1227/1299, 0
   disagree), the **round-trip oracle** (artifact 06 — render back to Ruby, run on CRuby,
   compare `obs⁺`; SSA'd output drifts far from source and makes the eval-order trace
   comparison much harder to review), the Lean decoder, and the **metatheory proofs**
   (`T5Loop`/`DispatchLoop` reason about concrete `(ctl, kont)` shapes).
5. **It contradicts the central design bet.** RubyCore deliberately mirrors Ruby closely
   (heads map 1:1 to Prism; `class`/`module` stay keyword heads to preserve cref/self). A
   second invasive normalization adds a correctness burden to the front end for the benefit
   of *one consumer* — and the front end is what everything else trusts.

**What survives from the intuition** is the good part: make dataflow explicit rather than
reconstructing it — but do it **dynamically**. A dynamic trace is *straight-line*, so it is
in SSA form **for free and φ-free**: every dynamic value is defined once and referenced by
id. That is §7's log, and it is why the log form is clean where the static form is messy.
(Same reason tracing JITs record linear traces in SSA.)

**Node IDs — honest scoping.** An earlier version of this argument claimed stable per-node
IDs in the export were a *prerequisite*. They are not: once the trace carries the condition
*term*, the engine needs no alignment at all, so the `DESYNC` failure mode disappears
without them. Node IDs remain a cheap, additive **nice-to-have for reporting** (source
attribution in witness output), independent of this design.

## 6. The recommended design (D2)

### 6.1 Term language

Serializable, small, and — per KLEE — with **no taint flag**: concrete ⟺ the term is `lit`.
Construction constant-folds, so fully-concrete arithmetic collapses to a literal
automatically.

```lean
inductive SymTerm where
  | inp   (k : Nat)                    -- the k-th symbolic input
  | lit   (n : Int)
  | un    (op : UnOp)  (a : SymTerm)   -- neg, succ, pred
  | bin   (op : BinOp) (a b : SymTerm) -- add sub mul; lt le gt ge eq ne
  | opaque                             -- NOT symbolically tracked
```

Three states, not KLEE's two. KLEE needs only (constant | expression) because it lifts
**all** of LLVM IR — a small closed instruction set. Ours is a *partial* lift of a language
whose effective instruction set is the whole method table, so `opaque` is unavoidable. It is
the price of partial lifting, and the same reason Rosette needs reflection.

Deliberately excluded for now: `/`, `%`, `**` (Ruby's flooring `Integer#/` does not line up
cleanly with z3's `Int`; per K7 they stay `opaque` rather than risk a wrong constraint), and
everything string/collection-valued (§8).

### 6.2 Shadow state

```lean
structure SymState where
  ctl     : SymTerm                          -- term of the in-flight value
  mirror  : List SymFrame                    -- parallel to m.kont
  locals  : List (FrameId × String × SymTerm)
  globals : List (String × SymTerm)
  notes   : List String                      -- frontier events
```

`mirror` runs parallel to `m.kont` and stores **only what the machine's kont does not
already expose**. The machine's kont is fully visible to the tracer, so `asgnK`/`ifK`/… need
no mirror payload; what does need it is `argsK`, which accumulates *values* whose *terms*
must ride along (receiver term + accumulated argument terms). Everything unmirrored
contributes `opaque` — safe by construction (constraint 2).

`locals` is keyed by `FrameId`, matching the model's frame store, so shared-scope closure
locals work naturally rather than being a special case.

### 6.3 The shadow step

```lean
def symStep (m m' : Machine) (s : SymState) : SymState × Array Json
```

Determined by `m`'s `(ctl, kont-head)` — the same discrimination `stepFn` performs — with
`m'` available to read concrete results. Representative rules:

| Pre-state | Shadow update |
|---|---|
| `eval (.int n)` | `ctl := lit n` |
| `eval (.var .gvar "$__inK")` | `ctl := inp K` — the input source (§6.5) |
| `eval (.var .lvar x)` | `ctl := locals[curFrame][x]` (default `opaque`) |
| `value v`, `asgnK .lvar x` | `locals[curFrame][x] := ctl` |
| `value v`, `recvK …` | mirror-push the receiver term (`= ctl`) for the coming `argsK` |
| `value v`, `argsK … acc rest …` | append `ctl` to the mirrored arg terms |
| `value v`, `argsK … acc [] …` (last arg) | if `mname` is a primitive op on integer operands and `m'.ctl` is a value: `ctl := bin op recvT argT`; else `opaque` + note |
| `value v`, `ifK`/`whileCondK` | emit `branch(cond := ctl, taken := v.truthy)` |
| method entry (frame pushed in `m'`) | bind param names in the new frame to the mirrored arg terms |
| anything else | `ctl := opaque`, append a note |

Two details: recognizing a primitive op needs **no reimplementation of dispatch** — the
method name is in the pre-state and the operand *values* are visible, and §6.4 then checks
the guess. Jumps/exceptions need no special handling: the mirror is popped whenever the
observed `kont` shortens.

### 6.4 Self-check — the shadow validates itself against the concrete run

Every `SymTerm` assigned to `ctl` is a claim about *this* run: evaluating it at the actual
inputs must equal the machine's actual value. So carry the concrete input vector and check

```
eval SymTerm inputs  ==  the concrete value the machine just produced
```

Mismatch ⇒ the shadow is wrong (a mirroring bug, or an op that doesn't mean what we
assumed) ⇒ set `opaque`, note it, continue. Consequences:

- mirroring bugs degrade to **lost precision, never wrong constraints**;
- the check runs on every difftest program for free, so the corpus doubles as a validation
  suite for the shadow;
- "the shadow drifts as the model grows" — the main worry about D2 — is **detected
  automatically** rather than surfacing later as a bad witness.

### 6.5 Inputs: a reserved global, so nothing is rewritten

The distinguished input source is the **global variable** `$__inK`. Rationale:

- Prism parses `$__in0` unambiguously as a gvar read (a bare identifier would be a *vcall*,
  not a local read), and it exports as `["var","gvar","$__in0"]` — **name-distinctive**, so
  the tracer can recognize it soundly without node IDs.
- The tracer preloads `m.globals` from `--inputs 31,7`, so **no AST rewriting** happens
  anywhere (retiring K4's substitution machinery) and multiple inputs fall out.
- **Zero model changes** — globals already work.

Rejected alternatives: substituting `__input__ → ["int", n]` (then a literal `31` elsewhere
is indistinguishable from the input — unsound); a new `Expr` head (touches the SUT); a
preloaded *local* (Prism reads an unassigned bare name as a vcall).

### 6.6 Trace format

```json
{ "branches": [ { "kind": "if", "taken": false,
                  "cond": ["bin","eq",["bin","add",["bin","mul",["inp",0],["lit",3]],
                                                   ["lit",7]],["lit",100]] } ],
  "outcome":  { "kind": "typestuck", "class": "NoMethodError", "message": "…" },
  "frontier": [ "untracked op Integer#% (term opaque)" ] }
```

`"cond": null` means the condition was `opaque`: the engine records no constraint and
surfaces a frontier line. Outcome classification is unchanged.

### 6.7 What the engine becomes

`collector.py`'s traversal disappears. The engine keeps: run via Lean → read `cond` terms →
translate term JSON to z3 (~30 lines, the irreducible "what does `+` mean to the solver"
map) → flip, solve, queue. No AST, no scopes, no order alignment, and `DESYNC` ceases to
exist as a failure mode.

## 7. Staging

| Stage | Content | Removes |
|---|---|---|
| **S1** | `SymTerm` (constant-folding), shadow with `locals`/`globals` + `argsK` mirror, primitive arithmetic/comparison, `if`/`while` conditions, self-check, term emission | dataflow through assignments and arithmetic — `derived.rb` |
| **S2** | param binding at method entry; return values | dataflow through calls — `nil_dispatch.rb` |
| **S3** | engine consumes terms; delete `collector.py`'s traversal; `--inputs` replaces AST substitution | the AST walk, `DESYNC`, K4 |
| **S4** | prediction-accuracy harness over tier-1 programs | the "is the shadow keeping up?" blind spot |

Note S1 and S2 are less separable in Ruby than in a C-like language, because **arithmetic
is dispatch** — `n * 3` is a send. S1 therefore already needs the `argsK` mirror; what S2
adds is user-method entry/return.

## 8. Honest hard parts and open questions

1. **Residual coupling — it moves, it doesn't vanish.** The mirror needs a rule per kont it
   wants precision on (the model has 41 `Kont` constructors; ~11 matter for the integer
   fragment). Strictly better than D0 — the coupling now lives in Lean next to the
   semantics and is checked by §6.4 — but only D3/D4 remove it.
2. **Heap dataflow is the biggest precision hole.** §6.2 tracks locals and globals only. A
   symbolic value written to an ivar, array element, or hash and read back is lost to
   `opaque` — exactly the case KLEE handles with arrays + `ReadExpr`. For Ruby, where state
   lives on the heap, this is significant, not a corner case. Fix: theory-of-arrays over the
   object store, with a KLEE-style per-slot concrete fast path so we don't pay symbolic
   costs where nothing is symbolic. **Deferred, and the top precision item after S3.**
3. **Truthiness of non-boolean conditions.** Ruby branches on any value; `truthy t` must
   mean "neither `nil` nor `false`". For integer terms that is trivially true — a useless
   constraint — so `if x` (as opposed to `if x < 5`) is not flippable until the term
   language gains a value-shape notion (is-nil / is-false). **Open.**
4. **Division/modulo** left `opaque` (K7). Modeling them means committing to z3 encodings of
   Ruby's flooring semantics, worth differential-testing against CRuby *on the encoding*.
5. **Strings and collections** out of scope; when they arrive the solver question changes
   (cvc5 string theory, array/sequence encodings) and the term language needs sorts.
6. **Blowup, not bugs, will bind.** Serval's experience (§3) says the limiting factor is
   symbolic-evaluation performance. Combined with `bounded-effect-checking.md` §7's path
   explosion, this argues for keeping the **concolic** discipline (concrete boot, one path at
   a time) rather than drifting toward whole-program symbolic execution — regardless of how
   dataflow is represented.

## 9. Symbolic dispatch — the payoff this enables

The type errors that matter are dispatch-dependent: *which class* a receiver has depends on
the input. Once terms exist, the natural next step is a term for `classOf(recv)` and
constraints like `classOf(recv) ∉ {classes defining m}` — **solving directly for inputs that
force a dispatch miss** rather than stumbling onto them via arithmetic guards.

The mechanism is Rosette's, correctly understood (§3): a receiver whose class depends on the
input is a **symbolic union over classes**; `for/all` enumerates the guarded candidates, runs
the **real concrete dispatch** per candidate (no symbolic model of dispatch needed — the
semantics already does it), and merges, leaving the guards as solver constraints.

The precondition is a finite, enumerable candidate set — which is **exactly what concrete
boot delivers**, since the class table is settled and fixed before symbolic execution
begins. So the design's two escape hatches should be distinguished:

- **`opaque`** — precision-losing, for genuinely untrackable arithmetic;
- **guarded split** — precision-preserving, for finite domains (classes, later small
  collections), which is where type-error hunting actually lives.

This is the mechanism `type-safety-by-reachability.md` §3 describes and §7 ranks as the
central difficulty. Out of scope for S1–S4; the reason to build this layer at all.
