# `Denote/Sem/notes.md` — the semantic ratchet: how a rung gets climbed

`Denote/notes.md` records why the *denotation* is shaped as it is. This file is about the
second ladder built on top of it: **one rung, one `Judge` rule discharged over that
denotation, proved from `stepFn`.** It is a working procedure, not a design essay — read it
before attempting a rung.

## The pieces, and which of them you never edit

| File | What it is | Hand-edited? |
|---|---|---|
| `Trans.lean` | `toRuby : Ratchet.Expr → RubyCore.Expr` | only when a syntax constructor changes |
| `State.lean` | `Evals`, `StateOk` and its twenty components | yes — a rung that will not close often means a component is wrong |
| `Judge.lean` | the eight `SemJudge*` definitions | yes, same reason |
| `Obligations.lean` | the 83 `Obl.*` — **derived** from the inductive | **no** |
| `../Ladder.lean` | the count, and the `isDefEq` gate | no — except its one `import Denote.Rules` |
| `../Rules.lean` | the list of rule files, so the ladder can see them | yes, one line per new file |
| `../Adequacy.lean` | `AdequacyTarget`, `AdequacyHyps` (derived) | no |
| `../Ext.lean` | `Ext` (allocation) and the probe lemmas across it | yes — a new allocation shape may need a clause |
| `../Grow.lean` | `denM_ext`: a type's meaning survives an allocation | no — it follows `Den.lean` |
| `../Local.lean` | `denM_setLocal`: … and a rebinding, given `capStale` | no — same |

The obligations are derived, not transcribed, and that is the load-bearing decision:
`SemJudge` was given *exactly* `Judge`'s signature so that a rule's obligation is its
constructor's own type with one constant swapped for another. Consequences worth keeping in
mind while working:

* **You cannot make an obligation easier.** If a rung will not close, the options are: prove
  it, fix a `StateOk` component, fix a `SemJudge*` definition, or fix the *rule* in
  `Ratchet/Judge.lean`. Editing the obligation is not on the list, because there is nothing to
  edit.
* **A rung claimed under the right name with the wrong statement does not count.** The ladder
  checks `isDefEq (type of Sem.X) Obl.X`. Verified: a `Sem.Judge.intLit : True` is not counted,
  a `Sem.Judge.fltLit : Obl.Judge.fltLit` is.
* **The denominator is live.** Add a rule to `Ratchet/Judge.lean` and 83 becomes 84 on the next
  build, with the new rule listed as undischarged. This is the opposite of the corpus norm
  ("a ratchet whose number depends on a live sample is not a ratchet") and for the opposite
  reason: the rule set is not a sample of the specification, it *is* the specification, so a
  committed copy of it would be the drift.

## Climbing one

1. `lake exe semladder` — the next rules up, in the inductive's own order.
2. Read the obligation. `#print Ratchet.Denote.Obl.Judge.intLit` gives it verbatim, premises
   and all.
3. Write `theorem Sem.Judge.intLit : Obl.Judge.intLit := …` in a file under `Denote/Rules/`
   (one file per tier or per family). The name must be exactly
   `Ratchet.Denote.Sem.<Family>.<rule>`, and the file must be listed in `Denote/Rules.lean` —
   the ladder counts what is in *its own* import graph, so an unimported rung does not exist.
   `Denote/Rules/Core.lean` holds the lemmas that are about the machine rather than about a
   rule (`denM_ctl`, `StateOk_reCtl`, `evals_pure`); reach for it before re-deriving one.
   `Denote/Rules/Alloc.lean` holds the same for an *allocating* step (`ext_push`): if the rule
   pushes a literal, the `Ext` it needs is one application away.
4. `lake exe semladder` again. The number moves or the type was wrong.

## What the proof of a rung looks like

Every obligation bottoms out in `Evals m e v m'` — "evaluating `e` from `m` returned `v`,
leaving `m'`" — and `Evals` is `∃ fuel, Interp.run fuel (evalFrom m e) = .value v m'`. So a
rung is: **invert the run**. For a literal that is two steps:

```
evalFrom m (.int n)          -- ctl := .eval (.int n), kont := []
  ⟶ stepFn: evalExpr        -- ctl := .value (.int n)
  ⟶ stepFn: applyKont []    -- .done (.int n) m
```

so any `fuel ≥ 2` gives `.value (.int n) m`, and `fuel < 2` gives `.outOfFuel` — which is not
a `.value`, so those cases close by contradiction. From `Evals` one therefore extracts
`v = .int n ∧ m' = m`, and the rest (`denM .int m (.int n)`, and `StateOk` unchanged) is
immediate. Expect a `match fuel with | 0 | 1 | k+2` at the top of most leaf rungs.

The compound rungs are the same move with the continuation stack in play, and the reason
`Evals` sets `kont := []` is exactly that: the expression's own value becomes the run's
result, so a `seq`'s rung can talk about its statements' runs without reasoning about what the
*caller's* continuation would have done with them.

## The three places a rung is expected to stall — recorded in advance

Writing these down before the first attempt, because a rung that will not close is
information about a definition rather than about the prover, and it is worth knowing which
definition to suspect.

1. **`StateOk`'s components.** Eleven of them, one per `Ctx` field plus `Γ` and `I`, and two
   are `True` (`ClosuresOk`, `PrivConstsOk`) with docstrings saying why. If a rung needs a
   fact about the heap that no component supplies, the component is missing, not the proof.
   `AsmsOk` is the one to watch: it is a claim about *running* calls, so it is the component
   that carries the conditionality `Judge`'s own docstring describes ("read a derivation with
   a non-empty `κ.asms` as a conditional claim") — and `Judge.callDef`'s rung is where that
   circularity has to be cut for real, by induction on something that decreases rather than by
   assuming the conclusion.
2. **`SemJudgeNested`** reads one level deep and leaves the recursion to `JudgeNested.cons`'s
   own obligation. If that is too weak, the symptom is `Obl.Judge.classStmt` refusing to close.
   Stated in its docstring as a recorded risk.
3. **Frame balance.** `SemJudge` concludes `m'.stack = m.stack`, which every rule that pushes
   a frame (a call, a block, a class body) must restore. Leaf rungs get it free; the call rungs
   will not, and that conjunct is where a bug in a frame-pushing rule would surface.

## The fourth stall point — observed, not predicted: **allocation** *(RESOLVED, clink 45)*

The three above were written before the first attempt. The first rung actually to stall was
none of them. `Judge.strLit` — the third literal, and by the count above a two-`stepFn`
rung like the others — did not close, because `evalExpr` on a `.str` calls
`Builtins.allocStr`: its post-machine's heap is its pre-machine's heap with one object
**pushed**. That is the first rung whose `m'` differs from `m` anywhere but `ctl`, and it
needed two things nothing then supplied.

1. **`StateOk` said nothing about the boot classes.** The rule concludes `.cls "String"`,
   whose denotation is `isAName m'.heap v "String"` — which resolves the *name* through the
   heap's constant table. A machine conformant with `(κ, Γ, I)` was not required to have a
   class named `String` at all, so the conclusion was not derivable from the hypothesis.
   Stall point (1) exactly as described above, and the missing component was a real one.

2. **`denM` did not survive a heap extension.** Re-proving `EnvOk Γ m'` means transporting
   `denM τ m (m.getLocal x)` across the push for an arbitrary `τ` — including an arrow, whose
   denotation quantifies over *runs* (`Returns m f args v m'`). A run from the extended heap
   allocates at shifted object ids, so it is not the run from the unextended one; relating the
   two is an allocation-equivariance simulation over the whole interpreter, not a lemma.
   `AsmsOk` has the same shape and had the same problem.

### How it was resolved, and what the resolution cost

**Both `StateOk` components (1) asked for were added**, `HeapSaturated` and `CoreOk`
(`State.lean`), and both are spent by the `strLit` rung: `CoreOk` on the conclusion and on the
dangling-reference case below, `HeapSaturated` on `ancestors`. The second is the one worth
knowing about in advance, because it is invisible until you look: `ancestors` is **fuel-bounded
by `h.objs.size + 1`** (a `partial def` would be opaque to the kernel, `RubyCore/Heap.lean`
L73), so pushing an object moves the *fuel* and the walk at `m` and the walk at `m'` are two
different computations. `RubyCore/Proof/AncestorsGrow.lean` had already solved exactly this —
`Saturated` ("one more unit of fuel changes nothing") plus `ancestors_congr_grow` — so it is
**imported**. That makes `Denote/Ext.lean` the first file in the package to depend on
`RubyCore.Proof.*` rather than only on the interpreter; the argument is
`Semantics/Interp.lean`'s, one layer up (a second copy of a proof about the same `stepFn` is a
second thing to drift).

**(2) was fixed in the definition, not worked around.** The arrow is the *only* arm of `denM`
that does not survive an allocation, so the arrow is what changed: both arrow arms — and
`AsmsOk`, which has the same shape — now read `∀ m₂, Ext m m₂ → …`. `Ext` (`Denote/Ext.lean`)
is the "coarser seed" this section previously said any such fix would need: same frames, same
stack, a heap that only grew. It is reflexive and transitive, so `Ext.refl` recovers the
unquantified reading (the change is a **strengthening** of `denM`, not a weakening) and
`Ext.trans` makes the arm monotone *by construction* — `denM_ext` (`Denote/Grow.lean`)
re-derives nothing about runs. And it reads neither `ctl` nor `kont`, which is precisely what
`Reaches` could not do; `denM_ctl` survives unchanged (`Ext_reCtl`).

**The one genuinely surprising cost: `Heap.get` is total.** Past the end of the heap it
answers `default`, whose `klass` is `0` — which is `Boot.basicObjectId`. So at a heap of size
`n`, the value `.ref n` is not an error: it is a **dangling reference that reads as an
instance of `BasicObject` with no ivars**, and after the push it reads as the pushed object.
Nothing in `StateOk` forbids `Γ` from typing a local that holds one, so the transport has to
survive it. `Ext`'s two fresh-id clauses (`freshIvars`, `freshBasic`) are exactly that, and
`CoreOk.basicSelf` is what collapses "any class the dangling read was an instance of" to the
single case `BasicObject`. Worth recording what was *not* needed: no heap-closedness or
value-boundedness invariant, because `default.payload` is `.none`, which makes
`arrayOf`/`hashOf`/`clos` vacuous at a dangling reference rather than in need of transport.

**Downstream, as predicted:** `Denote/Den.lean`, `Arrow.lean` (`ArrowFlat` stays, `ArrowExt`
is the quantified form, `denM_arrowOf` restated), `Rules/Core.lean` (`StateOk_reCtl` is now a
three-line corollary of `StateOk_ext` rather than a second component-by-component induction).
`DenB.lean` needed no change — it already answered `false` on both arrow arms — and the 31
`Examples.lean` guards are green, because they check `arrowCheck`, a `Bool`, and `ArrowFlat`
is what that is stated over.

## `Judge.vasgn` was unsound, and the obligation is what said so *(FIXED, clink 46; the twin rung climbed, clink 47)*

Before the wall below, the finding that came *out* of attempting `Judge.vasgn`: the rule is
**not true of `stepFn`**, and its obligation is false as written. Written up with the
reproducer in [`../../found-issues.md`](../../found-issues.md) §F1; the short form is that
`Judge.lambdaLit` records the creation-site environment into `Ty.clos`'s captured spine, a
Ruby block captures **by reference**, and `Judge.vasgn` invalidates `Ty.sameAs` aliases to the
assigned name but nothing about a `Ty.clos` over it. `x = 1; f = lambda { x }; x = "a";
f.call + 1` is certified `Integer` and raises `TypeError`.

Two things about *how* it was found are the point of this ladder existing:

* **No witness search was involved.** The obligation's conclusion asks for `StateOk` at the
  post-machine, whose `EnvOk` component asks for `denM (clos idx cap σ) m' f` — that is
  `denSpine cap m' (closLocal m' cl)`, the captured *frame's* locals read after the
  assignment. `Machine.setLocal` writes through the captured chain, so the spine no longer
  denotes. The definition of the obligation is the counterexample generator.
* **It names one rule.** `lambdaLit`'s obligation is fine (the spine does match `Γ` at the
  moment of creation); `closCall`'s is fine given a spine that denotes. It is `vasgn` that
  claims to leave the rest of `Γ` alone and does not.

Per the working procedure above, the rule was **not worked around**. It was *fixed*, in clink
46: `killClosOver`/`killClosOverSpine` (`Ratchet/Ty.lean`) widen every binding and ivar-spine
entry whose type records a stale capture of the assigned name, and a `capStale x τ τ = false`
`autoParam` premise covers the half that cannot be widened (`x = lambda { x }`, where the
stale record is in the type being bound). Three corpus rungs and two `CheckRungs` controls pin
it; `found-issues.md` §F1 has both reproducers and what is still open.

**`Judge.vasgnAlias` is now discharged** (clink 47, `../Rules/Asgn.lean`) — the twin whose
right-hand side is a `.var`, so its whole run is four concrete `stepFn` steps and the lemma
below is not needed. Its proof is where the fix is cashed: `capStale` is the *side condition*
of `denM_setLocal`, so the predicate the checker widens bindings with is the predicate the
transport needs. Three definitions moved to let it close, and each is a correction rather than
a convenience — `Later` (the arrow's and `AsmsOk`'s quantifier, now allowing a rebinding),
`StateOk.frameInRange` (there *is* a current frame), and `EnvOk`'s identity conjunct becoming
`Value` equality rather than the model's `equal?`, which is wrong in both directions at
`Float`. `Judge.vasgn` itself stays undischarged, and no longer for a soundness reason: it
waits on the lemma below.

## The fifth stall point — **the continuation frame**, and it is a wall rather than a step

`Judge.vasgn` is the first *compound* rule on the ladder, and it does not close for a reason
that has nothing to do with assignment. Measured, not guessed:

`Evals m e v m'` runs `e` with `kont := []`, deliberately (see `State.lean`'s docstring: the
expression's own value becomes the run's result). But `Judge.vasgn`'s obligation hands you a
run of `.vasgn .lvar x e`, whose first `stepFn` step is
`.next (withKont m (.eval rhs) (.asgnK kind x))` — so `e` runs with `kont := [.asgnK …]`, and
the premise `SemJudge κ Γ I e τ Γ' I'` is about a *different run*. Using the premise at all
requires a **decomposition lemma**: a run of `e` under continuation `K` passes through the
state that delivers `e`'s value to `K`.

The good news, checked: `stepFn` is **head-local in `kont`**. `applyKont` and `unwind` each
read only `m.kont`'s head and pop exactly one; every other producer *pushes*
(`grep 'kont :='` across `Interp*.lean` finds thirteen sites, all `k :: m.kont`). So the
lemma is true, and its shape is the obvious one:

```
stepFn m = .next m'  →  stepFn { m with kont := m.kont ++ K }
                          = .next { m' with kont := m'.kont ++ K }
```

with two exceptions that are exactly the "passing through" points: `applyKont` at `[]`
(`.done`) and `unwind` at `[]`. The second needs its own small lemma — a run that reaches
`unwind` with an empty continuation cannot end in `.value` (every arm is `uncaught`, `stuck`,
`unsupported`, or a `raiseErr` that becomes `uncaught` one step later) — which is why the
decomposition holds for exactly the runs `SemJudge` quantifies over.

**The size — measured in clink 50, and the first estimate was too pessimistic.** The
paragraph this replaces sized the lemma by inspection at "~1700 further lines … and past those
sit the builtins … ~24k lines", from the observation that `cases e <;> unfold <;> simp only
[withCtl, withKont] <;> cases h <;> rfl` closes only **12 of `evalExpr`'s 43 arms**. Run
against the real `stepFn` with one more tactic in the chain:

```
cases e <;> simp only [evalExpr, frameR, withCtl, withKont] <;> (repeat' split) <;> rfl
```

every arm whose body does not *delegate* closes, and the residue is not a long tail of hard
goals — it is **one goal per helper function**, each of exactly the same shape
(`helper (pk m K) args = frameR K (helper m args)`). Checked on `startArgs`, the worst case in
the residue: the same one-liner reduces it to a single goal naming `finishSend`, i.e. to
`finishSend`'s own framing lemma. So the shape of the job is a **dependency chain of one-line
lemmas over a bounded helper set** — `Interp/{Dispatch,Send,Reflect,Support}.lean` declare on
the order of thirty machine→`StepResult` helpers — rather than a line count proportional to
the interpreter. `frameR K` is the wrapper the statement needs (`.next m ↦ .next {m with kont
:= m.kont ++ K}`, every other outcome unchanged), and it works because `(k :: m.kont) ++ K`
and `k :: (m.kont ++ K)` are definitionally equal, so a pushing helper frames by `rfl`.

### … and the lemma as stated is **FALSE** *(clink 52)*

The measurement above checked the *writers* — "grep `kont :=` across `Interp*.lean` finds
thirteen sites, all `k :: m.kont`" — and that is the wrong half of the question. `stepFn` has
one **reader** of the continuation below the head, and one is enough:

```
-- RubyCore/Interp/Reflect.lean, the "throw" arm of tryReflect
let matched := fun (tag : Value) =>
  m.kont.any fun k => match k with | .catchK t => t.identEq tag | _ => false
```

`throw` with no matching `catchK` anywhere on the stack raises `UncaughtThrowError` **at the
throw site** — deliberately, so an enclosing `rescue` sees it — and with one, it jumps. So a
state whose own `kont` has no matching tag steps differently under a `K` that supplies one.
`Denote/Sem/Frame.lean`'s **`not_KontFrame`** is that counterexample, at the smallest machine
that reaches the dispatch (a value in flight, one `argsK` delivering it to an implicit-self
`throw`, an empty heap so the walk misses and reaches `tryReflect`). Conditional on two
`#guard`ed `Bool`s, because `Interp.invoke` is well-founded-recursive and therefore not
`rfl`-reducible — the same trade `../Sanity.lean`'s `bootOkB` makes.

**`EvalsDecompose` is false too, and that half is sharper.** It is not rescued by "the sub-run
must return", because a sub-run can return under the empty continuation and *not* under `K`:

```ruby
catch(:t) do
  x = begin
        throw :t
      rescue UncaughtThrowError
        1
      end
  x + 1
end
```

Under the empty continuation the `begin` **returns 1**; under the enclosing `catch` the same
`throw` leaves it entirely. So the run under `K` need not pass through the state that delivers
the sub-run's value to `K`, which is what the decomposition claims.

**The repair is a hypothesis, not a redefinition**, and it costs the rungs nothing:
`CatchFree K` — the appended tail carries no `catchK`. Every kont a `Judge` rule pushes is a
literal (`asgnK`, `argsK`, `seqK`, `arrK`, `hashK`, …), and a `catch` *inside* the
sub-expression pushes its `catchK` above `K` where both sides see it alike.
`KontFrameCatchFree` is the corrected target. Write the compound rungs against that.

Worth recording as a working lesson rather than an accident: the target was written down as a
`Prop`-shaped `def` with a name, which is why it could be *attacked* instead of assumed. A
comment saying "this ought to be true" would still be there.

### The `Builtins` **and `Interp/Support`** layers, proved *(clinks 52–53, `../../lean/RubyCore/Proof/KontFrame.lean`)*

Item 1 below — "the **builtins** are the genuinely open question … that is where the 24k lines
actually are" — was the reason this stall point looked unbounded. It is now measured, and the
answer is that these two layers are the *easy* ones:

* **Transparent by construction.** `grep -rn '\.kont\|kont :='` over the whole
  `RubyCore/Builtins/` directory finds **zero** occurrences. Above it, `Interp/Support.lean`
  touches `kont` in exactly one place — `withKont`, which conses — and that frames by `rfl`,
  since `(k :: m.kont) ++ K` and `k :: (m.kont ++ K)` are the same list.
* **`Builtins` is done, top to bottom** (108 theorems, axiom-clean): the leaves; both fuel
  walks; the five `…Impl` helpers; the `$~` layer (the one write that is not to the heap); the
  four continuation-taking helpers with the continuation's framing as a hypothesis;
  `runRegex`'s six `where` helpers; **all six dispatchers**; and **`Builtins.run`** itself. So
  the 24k lines the stall point feared are framed.
* **And all of `Interp/Support.lean`** came with it — `raiseErr`, `withCtl`/`withKont`,
  `setLocal`/`setGlobal`/`bindIvar`, `finishRegion`, `enterHandler`, `appendKwHash`,
  `spread`/`spreadA`, `doReturn`, `reifyBlock`, `coerceToProc`, `matchGlobal`, and
  `callClosure`, the first helper that pushes a *frame*.
* **What is left of the fifth stall point** is therefore `Interp/Reflect.lean`,
  `Dispatch.lean`, `Send.lean`, `Kont.lean` (`applyKont`/`unwind`, the two *conditional*
  statements), `evalExpr`/`stepFn`, `CatchFree` threading, and the one `partial def`.

Five tooling facts, each of which cost real time and none of which is in any manual:

1. **`rw [f.eq_def]`, never `simp only [f]`.** The equation compiler refuses per-arm equations
   at interpreter scale ("failed to generate equational theorem for `runModules`").
2. **`split` does not scale to deeply nested arms.** On `newImpl` (five nested `if`s) `split`'s
   own `simp` reports "maximum number of steps exceeded", and neither `maxSteps` nor
   `simp.maxSteps` is a settable option — hand case-splitting is ~15 lines per such function.
3. **`simp_all` must be a per-goal last resort, not a stage in the chain.** Run eagerly it
   *re-folds* goals that `rfl` would have closed; demoting it is what closed `callClosure` and
   four dispatchers that had looked blocked. This one lesson was worth four dispatchers.
4. **A lemma keyed on a lambda is invisible to `simp` and visible to `rw`.** The discrimination
   tree does not index under a lambda, so a fold-framing lemma has to be applied by `rw` — as a
   *conditional* rewrite, which is the trick: `rw` unifies the step out of the goal and leaves
   the framing hypothesis as a side goal, so the step (and its per-declaration matcher
   constant) never has to be written by hand — or by `exact`, where `isDefEq` unfolds matchers.
5. **A `macro_rules` tactic that mentions itself does not expand.** The first higher-order
   closer was written recursively and silently failed on every nested case; as a `repeat'`
   fixpoint it handles nesting for free.

**Three things the measurement does not settle****Three things the measurement does not settle**, and the next attempt should start from them
rather than from the good news:

1. ~~The **builtins** are the genuinely open question~~ — **settled, see above**: transparent,
   fast, and the residual is one dispatcher. `Interp/Support.lean` came with it. What is left
   of the fifth stall point is `Interp/Kont.lean`, `Send.lean`, `Dispatch.lean`, `Reflect.lean`
   and `evalExpr` — where the statements are *conditional* (item 2), `CatchFree` has to be
   threaded through the `throw` arm, and one `partial def` sits on the path (item 3).
2. `applyKont` and `unwind` have the two `[]` exceptions above, so their framing lemmas are
   **conditional** (on `m.kont ≠ []`), not unconditional. Only `evalExpr`'s is free of a side
   condition, which is also why the leaf rungs never needed any of this.
3. **One `partial def` sits on the chain and blocks it outright**: `destructureBind`
   (`RubyCore/Interp/Support.lean` L235), reached from `enterUserMethod`
   (`Interp/Dispatch.lean` L125) whenever a method has a destructuring parameter. A
   `partial def` compiles to an opaque constant with no equation lemmas, so *nothing* about it
   is provable by `rfl` or otherwise — this is the trap `../../AGENTS.md` L73 already warns
   about, arriving from the other side. The fix is the one `ancestors` already took
   (`RubyCore/Heap.lean` L73 is `partial`-free on purpose): give it a structural or
   fuel-bounded recursion. Its recursion is on nested `.destr` sub-params, so a measure on the
   parameter list's size is the obvious one. Two other `partial def`s are on the path
   (`Reflect.definesMethod`, `Builtins.pureOk`) and are **harmless** — neither takes a
   `Machine`, so both appear only as split conditions whose value is identical on the two
   sides.

Three things follow, and they are the reason this is written down rather than attempted:

* It is **not a `Denote/` lemma**. It is a structural fact about `RubyCore`'s abstract
  machine, and it belongs next to `stepFn` — in `RubyCore/Proof/`, where the metatheory
  already reasons about the continuation stack (by a *typed-stack invariant*, `KontOk`, rather
  than by decomposition — which is the technique that avoids needing this lemma at all, and is
  worth weighing before writing it).
* It blocks **most compound rungs**, not just `vasgn`: `if'`, `arrayLit`, `hashLit`,
  `JudgeSeq.cons`/`guard`/`nextGuard`, every call rule.
  **Two exceptions, both found by attempting them (clink 48), and both for the same kind of
  reason — the rule's premise is about a run nothing pushed a continuation for:**
  - **`JudgeSeq.last`.** `evalExpr`'s `.seq` arm is `| [e] => .next (withCtl m (.eval e))` —
    a *singleton* sequence pushes nothing, so the run of `.seq [e]` under an empty
    continuation *is* the run of `e` under an empty continuation, one `stepFn` step later
    (`../Rules/Seq.lean`). `JudgeSeq.cons`, whose first statement runs under `.seqK rest`, is
    the case that is still blocked.
  - **`JudgeRescues.cons`.** `JudgeRescues` threads no outgoing state, so its premise about
    the head handler is about *the same run* the conclusion asks about
    (`../Rules/Rescue.lean`). What it needs instead is the join, which is
    `../Join.lean`.
* The alternative — redefining `Evals` to quantify over continuations — is a **weakening of
  every obligation**, and must not be taken. `Evals` under an arbitrary `K` is strictly
  stronger as a predicate, and `Evals` sits on the *left* of `SemJudge`'s implication, so
  strengthening it weakens all 83 statements at once, silently, including the ten already
  climbed. The two forms are equivalent exactly when the decomposition lemma holds, which is
  the honest way to get there.

## The sixth stall point — **the declaration statement, and the context that goes stale**

Found by attempting `Judge.defStmt` (clink 48). **Its obligation is false**, and unlike §F1
this is not a bug in the rule — it is the shape of the semantic judgment meeting the shape of
`Judge`'s context threading.

`SemJudge κ Γ I e τ Γ' I'` concludes `StateOk κ Γ' I' m'`: the machine after the run still
conforms to **the incoming `κ`**. That is right for every expression whose effect is on values
and bindings, and wrong for every statement whose effect is on the *declarations* `κ`
describes:

```ruby
def foo; 1; end      # ①
def foo; "s"; end    # ②  <- Judge.defStmt, at a κ whose defs table still says foo returns 1
```

At ② the incoming `κ.defs` holds `⟨"foo", [], int 1⟩` (①'s entry, put there by
`JudgeSeq.cons`/`Ctx.afterStmt`), and a conformant machine really does have that method
installed — `StateOk` is satisfiable. `RubyCore`'s `defineMethod` **replaces**
(`h.setClassPayload … (name, md) :: methods.filter (·.1 != name)`), so at `m'` the installed
body is `"s"`, and `DefsOk κ.defs m'` — which asks for ①'s body — is false. `Judge.casgn`,
`Judge.cpathAsgn`, `Judge.classStmt` and `Judge.moduleStmt` are false for the same reason
(`ConstsOk`/`ClassesOk` in place of `DefsOk`), and so is `Judge.seq` at any sequence
containing one of them.

**The checker is not wrong here, and that was checked rather than assumed.** `Ctx.afterStmt`
conses the new entry and `defGet?` reads the *first* match, so the checker consults ②:

```
$ export-json <the program above, plus `foo`> | ratchet --stdin
{"type":"String","validate":true}          # and CRuby prints s
```

Two separate defects are tangled here, and only the first is fixable inside `State.lean`.

1. **`DefsOk`/`ClassesOk` quantify over the whole table** (`∀ d ∈ D`) while the checker only
   ever consults `defGet?`/`clsGet?`, i.e. the first match. So a stale entry is *required* to
   be installed, which makes `StateOk` unsatisfiable after any redefinition — every obligation
   at every later statement goes vacuous rather than false. That is a live vacuity risk of
   exactly the kind `../Sanity.lean` exists to police, and the fix is to state the components
   over the lookup function.
2. **`κ` is not threaded through the judgment.** Fixing (1) does not make `defStmt` provable:
   the *live* entry for `foo` at ② is still ①'s. The conclusion would have to be about
   `κ.afterStmt e τ` — which *is* expressible for `SemJudge` (every argument is in scope) and
   **is not** for `SemJudgeSeq`, whose accumulated context is a fold over statement types the
   signature does not carry. So the honest fix is a design decision about the semantic
   judgment's shape, not a lemma, and it wants its own clink. Note the fold direction is
   evidence the change is right rather than a workaround: `JudgeSeq.cons`'s obligation will
   need the first statement's conclusion at `κ.afterStmt` to feed the second's hypothesis.

Recorded here rather than in `../../found-issues.md` for the reproducer above, which is for
*wrong answers* and `validate` is right on that one.

### … and the blast radius is not statements. It is **every call rule**, and there it is a real soundness bug

Written after the paragraph above, from the obvious next question: a **call** runs statements
too. `Judge.vcallDef` — like `callDef`, `callMethod`, `selfCall`, `closCall`, `iterBlock` and
the rest — types the body and then concludes at the **same `κ`**, so a `def` *inside* a body
is recorded in the context that types the body and nowhere else, while at runtime it replaces
the installed method. That is not only an obligation that will not close; it is a program
`validate` gets wrong:

```ruby
def bar; 1; end
def foo; def bar; "s"; end; 1; end
foo
bar + 1        # CRuby and the model: TypeError.  validate: true, Integer.
```

Both executors **agree** on `TypeError`, so this is the §F1 shape exactly and it is written up
as `../../found-issues.md` §F3 — **fixed in clink 49**, conservatively: `declFree` filters
`defGet?`/`closGet?`, so a body that declares is *uncallable* by this checker rather than
callable-and-wrong. That closes the wrong answer and leaves this stall point standing, because
`Judge.defStmt`'s own obligation is the same problem one level up and needs the context
threaded through `Judge`'s signature.

Two things worth carrying forward:

* The stall point is what produced it. Nothing was searched for: `Obl.Judge.vcallDef`'s
  `StateOk κ Γ I m'` conclusion asks `DefsOk` of a table the body just invalidated, and asking
  *which* program does that is a two-line exercise once the obligation has been read.
* It sharpens the fix. The per-rule premise ("this body declares nothing `κ` records") and the
  signature change (`Judge … κ'`) are now both answering *two* problems — the declaration
  statement and the declaring call — which is an argument for the second.

## The seventh stall point — **an argument list is not a snapshot** *(RESOLVED, clink 53)*

Found by inspecting `SemJudgeAll` while attempting `JudgeAll.cons` (clink 48). Not yet
demonstrated false; the honest status is **unprovable as stated, for a reason that is one
`PrimSig` row away from being a soundness bug.**

`SemJudgeAll` concludes `DenAll τs m' vs` — *every* argument's type, checked at the machine
the *whole list* left behind. That is the right machine for the consumer (`Judge.prim` and the
call rules use the argument types at the moment of the call), and it means the `cons` rung
must transport `denM τ m₁ v` — the first argument's type, established where its own run
ended — across the evaluation of *every later argument*. There is no such transport:
`denM_ext`/`denM_ext`'s `Ext` demands a heap that only grew, and evaluating an arbitrary Ruby
expression can mutate objects.

What stops this from being a live unsoundness today is a property of the **table**, not of the
judgment: `PrimSig` has no row that can change a value's type in place. Grep finds no `[]=`,
`push`, `concat`, `replace`, `clear`, `insert`, `unshift`, `store` or `map!` row at all; the
only mutator is `arrayPush` (`<<`), whose signature `(.arrayOf τ) "<<" [τ] (.arrayOf τ)`
requires the pushed element to have the array's own element type, and `freeze`, which changes
nothing. So no *typeable* program can widen a container it has already typed — including the
empty-array case, where `.arrayOf .never` means every push is rejected for want of a `never`
argument.

Two consequences worth stating in advance:

* **A rung is not what will catch the regression.** The day an `Array#[]=` or `Hash#[]=` row is
  added, the *consumer* rules' obligations become provably false and this becomes a
  `found-issues.md` §F entry. Until then the ladder can only record the dependency.
* **The fix is a definition, and there are two candidates.** Either `SemJudgeAll` states each
  argument's type at *its own* post-machine (weaker, and then the consumer rules need the
  transport instead — moving the problem to where the values are actually used), or `StateOk`
  grows a non-interference component. Neither is free, and choosing wants the first call rung's
  requirements in hand.

### Resolved, clink 53 — the first candidate, and it climbed three rungs

The first candidate was taken: **`DenAllAt`** (`Judge.lean`) states each element's type at the
machine its own evaluation ended at, which is what an argument list's evaluation actually
establishes. The transport moves to the rules that use the values, and that is the argument for
this candidate over the other: a call rule that needs its arguments' types at the *call*
machine now has to say so, and `PrimSig`'s no-mutator property — the thing that makes the old
form true today — becomes an explicit obligation at the consumer instead of an invisible
dependency here.

The same clink fixed the second defect in the same family: **`SemJudgePairs` now interleaves**
(`pairExprs`: key, value, key, value), which is Ruby's order and the order `evalExpr`'s `.hash`
arm performs. Left as it was, `JudgePairs.cons`'s obligation was stated over an evaluation the
machine never performs — vacuity, not falsity, and `Judge.hashLit` would have had nothing
usable to consume.

**And the filing was wrong about the wall.** `JudgeAll.cons`, `JudgeKw.pair` and
`JudgePairs.cons` were also thought to be behind the *fifth* stall point. They never were:
`EvalsAll`'s `cons` arm is `∃ m₁, Evals m e v m₁ ∧ EvalsAll m₁ es vs m'`, so each element's run
is an `Evals` — under an **empty** continuation — and a hypothesis of that shape *is* the
premises' hypotheses. The companion families are **compositional by definition**, so no
companion rule ever needed the decomposition; the wall belongs to the *consumers*
(`Judge.arrayLit`'s own run pushes `arrK` per element). Same mistake, and the same direction,
as the one `../Rules/Nil.lean` records for `JudgeSeq.last`: **check whether the hypothesis is
compound before filing a rule behind the wall.** Six of the eight families are complete as a
result (`JudgeAll`, `JudgeKw`, `JudgePairs`, `JudgeRescues`, `JudgeConsts`, `JudgeNested`).

**A second, unrelated defect in the same family, found by inspection at the same time:**
`SemJudgePairs` reads a hash literal's pairs as `ps.map (·.1) ++ ps.map (·.2)` — **all keys,
then all values** — while `JudgePairs.cons` threads key, then value, then the rest, which is
Ruby's own order and the order `evalExpr`'s `.hash` arm performs. The two coincide at one pair
and diverge at two, so `JudgePairs.cons`'s obligation is stated over an evaluation order the
machine never performs. It is a *hypothesis*, so the effect is vacuity rather than falsity —
and `Judge.hashLit`'s rung would then have nothing usable to consume. Fix is one line in
`Judge.lean`'s `SemJudgePairs` (interleave the list); left for the clink that attempts the
rule, so that the fix is checked by a rung rather than by eye.

## The eighth stall point — **a table keyed by path, a rule keyed by name** *(RESOLVED, clink 50)*

Found by attempting `Judge.constEnv`. `ConstsOk` quantified over `Ctx.consts`' **entries**
while the checker only ever consults `constGet?`, and the two are keyed differently:
`Ctx.consts` uses absolute paths (`"::LIMIT"` at toplevel, `"::A::X"` for a constant declared
in `class A`) and the old component asked for `constLookup m.heap (stripColons p)` — a
*toplevel* constant literally spelled `A::X`, which no heap has. Two defects in one:

* the component was **unsatisfiable** at any context with a nested constant, so every
  obligation there went vacuous rather than false — exactly the failure mode `../Sanity.lean`
  exists to police; and
* it said nothing about the name `constGet?` actually resolves when `constEnv` fires, so the
  rung had no premise to spend.

This is the sixth stall point's item (1) — *"the fix is to state the components over the
lookup function"* — arriving at the first component that could be shown to need it, and it
was fixed that way: `ConstsOk κ m` now reads `∀ n τ, constGet? κ n = some τ → ∃ v,
constResolveAt m n = some v ∧ denM τ m v`. It takes the whole `Ctx` because `constGet?`
consults `κ.frame`'s class before the toplevel path. `Judge.constEnv`'s rung is three lines
after the change. **`DefsOk` and `ClassesOk` have the same defect and it is still open** —
they are the sixth stall point's own examples, and nothing has forced them yet.

The companion component the same clink added, `ConstScopeOk`, is the *other* half of the same
mismatch and is not resolved so much as scoped: `denM (.clsOf n)` resolves `n` through the
toplevel table while the machine runs CRuby's two-phase lexical rule, and `ConstScopeOk` says
the two agree. A machine standing inside a class body that shadows a constant is therefore not
conformant, and the four `.const` obligations say nothing there. That is the honest scope of
the rules as written — none of `constCls`/`constBuiltin`/`constExc`/`constEnv` has a premise
about the frame, and each concludes about the *toplevel* name — and a rule that wants the
nested reading needs `Ctx` to record the cref, which it does not.

## The ninth stall point — **a negative premise wants an upper bound, and every component is a lower bound** *(conformance half RESOLVED, clink 51)*

Found by attempting `Judge.bareName` and `Judge.lambdaLit` (clink 50); neither is climbed.

Every table component of `StateOk` is a **lower** bound: `DefsOk` says each entry of `κ.defs`
is installed, `ClassesOk` says each entry of `κ.classes` is a real class. Nothing says the
machine has *nothing else*. That is right — the prelude installs hundreds of methods no `Ctx`
mentions — and it is exactly what a rule with a **negative** premise needs and cannot get:

* `Judge.bareName` requires `defDeclared? κ.defs m = none` and concludes `.any` for
  `.vcall m`, on the strength of `m` raising `NameError`. A conformant machine may have
  `def x; @a = 1; end` installed and absent from `κ.defs`; then the call *returns*, and it
  leaves an ivar behind, so `SelfSpineOk`'s completeness clause fails at `I = .ivar0` and the
  obligation is false.
* `Judge.lambdaLit` requires `nameFree κ m = true` — no user `def lambda` — which is the
  §F2/§A5 fix (clink 49) stated over the checker's tables. Same gap on the machine side.

Not a soundness bug in either case, and that was checked rather than assumed: a program that
defines `x` puts it in `κ.defs` via `Ctx.afterStmt`, so `bareName` does not fire on it, and
`vcallDef`/`declFree` handle the rest. It is a **conformance** gap.

**Resolved on the conformance side in clink 51** — see [`Frame.lean`](Frame.lean), which is
where "and nothing more" is stated. It took three components rather than the one predicted:

* `MethodsExact` — the general upper bound. Every method installed anywhere in the heap is an
  axiomatized builtin, a prelude definition, or a name `κ` records. Measured at the booted
  heap before it was stated: **zero** methods are none of the three.
* `NameFreeOk` — because `MethodsExact` is not enough. It allows a *prelude* method, and
  `bareName` needs `x` to resolve to **nothing**; "not the user's" is not "not there". So the
  prelude escape is dropped on a fixed three-name list and the claim is localised to the
  receiver's chain. Chain-local because heap-global is **false**: the prelude defines `T.proc`
  (a singleton method on the `T` module), which is off every ordinary chain — so the model's
  own shadowing test is right and the component has to walk where it walks.
* `SelfLive` — `NameFreeOk` is about the chain at `self`, `classOf` reads the *total*
  `Heap.get`, so at a dangling `self` an allocation changes what `self` is an instance of.
  Nothing had said `self` is a real object.

All three are in `StateOk`, both transports go through, and `../Sanity.lean`'s `bootOkB` still
exhibits a model — so this is an upper bound that did **not** cost vacuity, which was the risk.

What remains per rule is no longer about conformance: it is the forward walk
`startArgs`/`finishSend`/dispatch down to the `NameError` (`bareName`) or to `reifyBlock`'s
Proc (`lambdaLit`). Neither needs the fifth stall point — both rules have no argument
expressions, so no sub-run is ever under a pushed continuation.

**Both walks were done in clink 52 and both rules are climbed** (`../Rules/Bare.lean`,
`../Rules/Lambda.lean`). Each cost one more piece of "and nothing more" than clink 51 had
supplied, and in both cases the piece was named by an interpreter test rather than guessed:

* `bareName` needed `lookup` to answer **nothing**, not "nothing of the user's" —
  `NameFreeOk` admits `builtin.isSome`, and a builtin named `x` would send `invokeDispatch`
  into `Builtins.run`. `BareNameFree` is that, at the rule's own premises. It also needed
  `MissFree`: `dispatchMiss`'s last question before raising is `method_missing`, and a user
  one makes the miss *return*. That is `../../found-issues.md` §F4 — a wrong answer both
  executors agree on, found by asking the question the walk asks, and fixed in the rule.
* `lambdaLit` needed `FrameInRange` to say the frame stack is **non-empty**, which the
  inequality alone did not: `closSelf` reads the captured frame *by id* while `SelfTyOk` reads
  `currentFrame`, and `Machine.currentFrame` answers `default` at `[]` while the captured id
  is `0`. Clink 47's docstring already claimed "there *is* a current frame"; now the component
  says it.

## The tenth stall point — **a spine is a lookup, and the checker really does build a duplicate key** *(RESOLVED, clink 52)*

Found by attempting `Judge.lambdaLit` (clink 52), and it is the sixth stall point's item (1)
for the *third* time: **state the component over the lookup function.** Here the component was
`denSpine` itself.

`denM`'s two spine arms (`.inst`'s ivars, `.clos`'s captured locals) read a spine with
`denSpine`, which walked **every** `ivarCons` entry. Every *consumer* of a spine — `ivarGet?`,
and `envGet?` for the environment a spine is made from — answers with the **first** match. The
two coincide on a duplicate-free spine, and `ivarSet`/`joinSpine` keep ivar spines
duplicate-free, so nothing had forced the question. `envToSpine` does not:

```ruby
x = 1
f = lambda { |x| lambda { x } }
g = f.call("s")
g            # validate: <closure#1>{x: String, x: Integer} -- and it is *right*
g.call + 1   # correctly rejected; `g.call` is a String
```

`Judge.closCall` types a lambda's body in `paramEnv c.params argTys ++ spineToEnv cap` —
parameters first, "so they shadow a captured name of the same spelling", as its own docstring
says — so a parameter shadowing a captured local is a duplicate **by design**, and the inner
`lambda`'s `envToSpine Γ` carries both entries. With the all-entries reading, `denM` of that
type demanded the captured frame's `x` be a `String` *and* an `Integer`, which is false of the
machine that holds it. So:

* `Obl.Judge.lambdaLit` was **false**, not merely unprovable; and
* worse, `EnvOk` at any environment binding such a `g` was false too, which made `StateOk`
  **unsatisfiable** there — every obligation at every machine holding a shadow-capturing
  closure went vacuous. That is the failure mode `../Sanity.lean` exists to police, and it is
  the second time (after the eighth stall point) that a component keyed differently from its
  lookup produced vacuity rather than falsity.

**The fix, and the two shapes rejected.** `denSpineFrom seen τ m g` (`../Den.lean`) carries the
keys already bound and *skips* an entry whose key is among them; `denSpine τ = denSpineFrom []
τ`. Two alternatives were considered and dropped, both for the same proof-shape reason:

* **`denSpine (dedup τ)` at the two call sites.** `dedup τ` is not a subterm of `τ`, so all
  four transports (`denM_heap_only_aux`, `denM_ctl`, `denM_ext`, `denM_setLocal`) would have
  had to become well-founded inductions on `sizeOf`.
* **`denSpine τ m g := ∀ x σ, ivarGet? τ x = some σ → denM σ m (g x)`**, the fully
  lookup-shaped form. Cleanest to *read*, and it makes `denSpineFrom_get` an identity — but it
  breaks the mutual block's structural recursion (the recursive call is at a `σ` that comes
  from a hypothesis, not a pattern), and every transport then needs an extra induction to
  recover "σ is a component of τ".

With the accumulator the recursion stays structural and each transport carries one extra
`∀ seen`. What the fix cost, precisely: the `seen` parameter through `denSpineFrom`,
`denSpineBFrom` (the `Bool` twin, so `closB_sound` and `Examples.lean`'s guards still line
up) and the four transports; `denSpineFrom_get` gained an `x ∉ seen` side condition,
which is exactly the invariant the walk maintains. Two new `Examples.lean` guards pin the
behaviour at the real semantics (a shadowed entry is skipped; a *wrong first* entry is not
rescued by a right second one), taking that file to **33**.

**Read it as a definitional correction rather than a convenience**, by the same test the
fourth stall point used: the new reading is what the checker's own consumers mean, the old one
was a strictly stronger demand that no rule and no `Judge` premise ever made, and the machines
that separated them were real.

## The eleventh stall point — **a `def` is not an allocation**, predicted rather than met

Not reached by a rung; derived while asking whether the sixth stall point's item (2) could be
worked around *inside* `Denote/Sem/Judge.lean` (which is hand-editable) instead of in
`Judge`'s signature (which is not, under this clink's constraints). Recorded because the
answer is interesting and it is the next attempt's problem.

**The workaround does exist, halfway.** `SemJudge` could conclude `StateOk (κ.afterStmt e τ)
Γ' I' m'` — every argument is in scope, and `afterStmt` is the identity on every
non-declaration expression, *definitionally* (a structure update with unchanged fields), so
the 30 climbed rungs would be unaffected. `SemJudgeSeq` still cannot express it, which is the
half the sixth stall point already recorded.

**What stops `Judge.defStmt` even with that in hand** is a transport, and it is the fourth
stall point one level up. `evalExpr`'s `.def'` arm installs the method with
`Heap.setClassPayload`, so the post-machine's `classPayload?` at `Object` **differs** — and
both future relations demand it not:

* `Ext.payload : ∀ k, m₂.heap.classPayload? k = m.heap.classPayload? k`, and `Later` has the
  same clause. So `StateOk_ext` does not apply, and neither does anything built on it.
* Component by component, most of `StateOk` survives a method installation by inspection
  (`procClosure?`, `ivarOf`, `getLocal`, `constLookup`, `ancestors` — `defineMethod` touches
  one class's `methods` list and nothing else). **Two do not**, and they are the two that
  quantify over *runs*: `denM`'s arrow arms (through `EnvOk`) and `AsmsOk`.

And the honest reading is that they *should* not: an arrow is a claim about what calling a
value returns, and installing a method can change exactly that. `f = lambda { foo }` followed
by a redefinition of `foo` is the shape — the same shape as `../../found-issues.md` §F1, with
a `def` in place of an assignment. So the fix is not a coarser quantifier (which would be
false); it is the §F1 fix's analogue: **a declaration invalidates recorded claims about calls**,
which is a `killClosOver`-style widening keyed on declarations rather than on assignment.

Two reasons this is filed as a prediction rather than a §F entry, both checked:

* the checker does not **infer** an arrow anywhere (`Denote/Arrow.lean`: `ArrowStable` "is not
  what the checker infers today"), so a `Γ` carrying one is a conformance shape rather than a
  reachable judgment — the exposure is vacuity, not a wrong answer; and
* `AsmsOk`'s rows are the checker's recursion device and are *discharged* by the same rule that
  adds them, so a stale row is a conditional claim rather than a belief — which is what
  `Judge`'s own docstring says to read a non-empty `κ.asms` as.

## Where the remaining 50 rules actually sit

Written at 30 of 83, because "53 remaining" is not 53 units of work and the shape of what is
left is the useful fact. Every remaining rule is behind at least one of three walls, and none
of the three is a proof that a rung can carry on its own:

| Wall | What it is | Rules behind it |
|---|---|---|
| **5th** — `KontFrame` (now `KontFrameCatchFree`) | a sub-expression runs under a pushed continuation, so a rule's premise is about a *different run* than its conclusion | every rule with a sub-expression: `vasgn`, `ivarAsgn`, `if'`, `ifNoElse`, `begin'`, `while'`, `constPath`, `constPathCls`, `primNever`, `raiseCls`, and all of `JudgeSeq.cons`/`guard`/`nextGuard` |
| **6th (2)** — `κ` not threaded through `Judge` | a run that *declares* invalidates the incoming `κ`, which the conclusion re-asserts | the five **statement** rules: `defStmt`, `classStmt`, `moduleStmt`, `casgn`, `cpathAsgn` (and the 11th above is the transport each of them then needs) |
| **the call lemma** — unwritten, and not yet a stall point because nothing has attempted it | a premise about the *body*'s run, from the machine `enterUserMethod` builds, has to be related to the call's run — plus the frame-balance conjunct `m'.stack = m.stack`, which every frame-pushing rule owes | every call rule: `callAsm`…`yieldExpr`, `vcallAsm`, `vcallDef`, `new*`, `iter*`, `super*` |
| **7th** — ~~`SemJudgeAll`'s snapshot~~ | **resolved, clink 53**; what is left of it is the *transport* a consumer needs to move an argument's type to the call machine | the consumers only: `arrayLit`, `hashLit`, `prim`, `isAQuery`, `caseEqQuery`, `classOf`, `clsToS`, the `call*`/`new*`/`iter*` rules — and each of those is behind the 5th anyway |

**Correction worth making explicit, because the sixth stall point's own text overstates its
reach**: the call rules are *not* behind it. Clink 49's `declFree` filter lives inside
`defGet?`/`closGet?` (and therefore inside `mroGet?`/`smroGet?`/`resolveAliases`), so a body
that declares anything is **uncallable** by this checker — which means every call rule's
premise already implies its body declares nothing, and the incoming `κ` survives the body.
What blocks the call rules is the 5th and the 7th, plus a call lemma nobody has written.

The three companion `cons` rules are climbed (clink 53) and were never behind a wall at all —
see the seventh stall point. The two rules behind the **9th** (conformance as an upper bound)
are climbed, and
that was the last wall a single clink could take down by adding components. What is left needs
one of: a metatheorem about `stepFn` that belongs in `RubyCore/Proof/` (5th), a change to
`Judge`'s signature and therefore to all 177 derivations (6th), a design decision about
`SemJudgeAll` (7th, and its two candidate fixes want the first call rung's requirements in
hand), or the call lemma.

## What is not on this ladder

**Stuck-freedom.** `SemJudge` is partial correctness about the *value*: a run that returns
lands in the type's denotation. It says nothing about whether a run reaches a type-stuck
outcome — the `NoMethodError`/`ArgumentError`/`TypeError` family
`../../type-safety-by-reachability.md` is about, and the property `Ratchet/`'s whole soundness
story ultimately wants. `StuckFree` (`State.lean`) and `StuckFreeTarget` (`../Adequacy.lean`)
state it; nothing counts it. Folding it in would make every rung carry two proofs of different
shapes under one number, and the ladder's number is supposed to mean one thing.
