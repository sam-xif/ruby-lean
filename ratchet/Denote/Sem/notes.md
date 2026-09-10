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
* **`Interp/Dispatch.lean`, most of it** (clink 53, third pass): `destructureBind` — the item
  that was blocked *in principle* — plus `eigenclassOf`, `symOrStr`, `mixinShadow`,
  `moduleHook`, `missNoMethod`, `visError?`, `cpathContainer`, `defineAttr`, `enterClassBody`
  and `enterScopedClassBody`. The frame-pushing entries live in a second module
  (`KontFrameDispatch.lean`) so that iterating on them does not recompile the first;
  `enterUserMethod` is `split`-bound on a 135-line body with ten branch points and is the one
  function whose build cost is measured in minutes.
* **The shape problem, named.** The interpreter builds machines by nested record update and
  Lean collapses those into one flat literal — so a machine that *is* `pushK K m'` is spelled
  with `kont := k ++ K` inline, and nothing whose left-hand side is `pushK K ?m` unifies with
  it. Two fixes do **not** work: `@[reducible] pushK` (the discrimination tree still keys on
  the literal) and a `@[simp]` lemma for the missing direction (simp then uses structure eta to
  expand every machine into nine field projections — a two-arm goal becomes ninety). What
  works is a *keyed* variant per callee (`eigenclassOf_frame_mk`) or a hand-written `show`.
* **And `frame_simp` must run before `split`**, or `split` peels the pushed and unpushed
  matches independently and pairs arm `i` of one with arm `j` of the other. The symptom reads
  as a false statement (a goal comparing a `raiseErr` against a `withKont`) and is nothing of
  the kind.
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
3. ~~**One `partial def` sits on the chain and blocks it outright**~~ — **fixed, clink 53.**
   `destructureBind` now has a fuel-bounded recursion (`destrDepth`, the nesting depth of
   `.destr` sub-params, passed by both call sites), which is the fix `ancestors` already took;
   the model's behaviour is unchanged (verified by hand against CRuby on
   `def f((a, b), c)` / `def g((a, (b, c)), *rest)`, and by the corpus agreement at 239/239).
   Its framing lemma is now ordinary work rather than impossible, and
   `../../lean/RubyCore/Proof/KontFrame.lean` records exactly what it needs. The original
   text follows, since the trap it describes is the general lesson: `destructureBind`
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

## Where the remaining 36 rules sit — **re-audited, clink 60**

The table above was written at 30 of 83 and three of its four walls have moved since. This is
the same census at 47, rule by rule, and its point is that **nothing on the list is one rung's
work**: every one of the 36 is behind one of four unbuilt layers, and no layer is smaller than a
clink.

| Layer | Rules waiting on it | Status |
|---|---|---|
| **The locals/frame invariant** (15th/16th/18th) | `if'`, `ifNoElse`, `begin'` | `Sealed`/`FramesWF`/`StepInv` built; the seal is **not inductive** (18th), so the invariant needs its control-state half before the interpreter walk can start |
| **The call lemma + jump-freeness** (13th/14th) | the 22 call rules — `callAsm`, `callDef`, `callDefKw`, `callMethod`, `callMissing`, `selfCall`, `superCall`, `zsuperCall`, `callSMethod`, `selfNew`, `selfSCall`, `closCall`, `iterBlock`, `iterSymPass`, `iterClosPass`, `callDefBlk`, `callMethodBlk`, `callSMethodBlk`, `selfCallBlk`, `yieldExpr`, `vcallAsm`, `vcallDef`, `newInst` — plus `while'`, which needs only the jump-freeness half (`break` in a `while` body *is* the loop's value, so the obligation is false without it) | unwritten. `Denote/Sem/Send.lean`'s `run_args` takes a call apart down to `finishSend`; what is missing is the activation between the frame push and its pop, and it cannot be *stated* without jump-freeness |
| **`κ` threaded through the judgment** (6th/17th) | `defStmt`, `classStmt`, `moduleStmt`, `casgn`, `cpathAsgn`, and **`JudgeSeq.cons`** — whose second premise is at `κ.afterStmt e σ` while its own hypothesis is at `κ`, so it is the same problem read from the consumer's end | a change to `Judge`'s signature, i.e. to all 178 derivations |
| **`PrimSig`, row by row** (13th, expensive end) | `prim` — one rule, ~200 facts about CRuby's builtins | the "list of named builtins" `../../type-safety-by-reachability.md` §9.0 already calls the remaining model-coverage job |
| **A falsity, not a layer** (7th's remnant) | `arrayLit`, `hashLit` | the transport a `DenAllAt` consumer needs is **false** (a later element can mutate an earlier one); the three candidate repairs are in §The seventh stall point's remnant and none is a one-liner |

**And the two closest rules are behind a falsity as well as a layer.** `Judge.if'`/`ifNoElse`
look one lemma away — all six narrowing type-lemmas are proved (clink 57), and
`Denote/Rules/NarrowInv.lean`'s `stateOk_narrow_then`/`stateOk_narrow_else` are the assembled
transports — but each is blocked *twice*: by the `&&` sandwich's `thenOnly` refinement (the
locals layer) **and** by the eleventh stall point, where `joinEnv` synthesizes an alias nobody
promised and the obligation is false as written. Worth stating plainly because it changes what
"next up" means: the ladder's own order (`semladder` prints the inductive's) puts `if'` first,
and `if'` is not the cheapest remaining rung — there is no cheapest remaining rung.

## The fifth stall point — **cleared** (clink 54)

`RubyCore.Proof.stepFn_frame` is `KontFrameCatchFree`'s statement, proved over the whole of
`stepFn` and axiom-clean; `Denote/Sem/Decompose.lean`'s `run_split` is the decomposition
`EvalsDecompose` was stating. `Judge.vasgn` is the first rung to spend them. See
`implementation-notes.md` clink 54 for the chain, the six tools that generalised out of it, and
the two facts the wall's own statement did not predict (`unwind`'s `retJ` arm *steps* at an
empty continuation, so the side condition is needed after all; and `.done` is constructed at
one site in the interpreter, which is what makes a run *invertible*).

Three hypotheses, not two: `CatchFree K` (predicted in clink 52), the side condition
(predicted, for the wrong arm), and **`JumpOpaque K`** — `K` cannot turn an escaping jump into
a returned value. The last one holds by computation for every continuation a `Judge` rule
pushes, since those are literals.

## The eleventh stall point — **the join can synthesize an alias nobody promised**

`Judge.if'`'s conclusion records `joinEnv Γ₁ Γ₂`, and the obligation is **false as stated**,
for a reason that has nothing to do with continuations or with narrowing. Take

```
Γ₁ = [(x, .union (.sameAs y .int) (.sameAs y .int))]     Γ₂ = [(x, .sameAs y .int)]
```

`joinT` finds no structural join (`σ ≠ τ`, neither is `.nilT`, neither is the other's
`.nilable`), so it takes the **union arm**: `unionMems Γ₁(x) ++ unionMems Γ₂(x)` is
`[A, A, A]`, `dedupTys` makes it `[A]`, and `unionOf [A] = A`. So the join records
`x : .sameAs y .int` — a claim that `m.getLocal x = m.getLocal y`.

What supports it? `EnvOk Γ₁ m` gives `denM (stripAlias (.union A A)) m (m.getLocal x)`, which
is `denM .int`, and **no identity claim at all**: `EnvOk`'s second conjunct fires only when the
recorded type *is* a `.sameAs`, and a union of aliases is not. So a machine with
`x ↦ 1, y ↦ 2` conforms to `Γ₁` and refutes the join.

Unreachable through `chk` — `joinT` of two aliases with the same target is caught by
`joinTy`'s `σ == τ` arm long before the union one, and nothing else builds a union of
identical aliases — so this is `found-issues.md` §F5's shape again: a rule unsound in
isolation whose soundness in the checker rests on an unstated invariant.

**Two candidate fixes, and the cheap one is not obviously right.**

1. **Strengthen `EnvOk`'s identity conjunct over `unionMems`**: require the identity for every
   alias *among the recorded type's members*, not only for a top-level one. Then the
   pathological machine is excluded and the join lemma goes through — the union arm's singleton
   dedup forces the alias to be a member of `Γ₁`'s entry, which is exactly what the
   strengthened clause asks about. **No `Ratchet/` change, so no gate risk.** The cost is that
   `StateOk_setLocal` must then *establish* the stronger clause, and `Judge.vasgn`'s §F5
   premise (`isAliasTy τ = false`) is no longer enough — it would have to become "no alias
   anywhere in `τ`", which is a different premise with a different blast radius.
2. **Make `joinT` strip aliases in its union arm.** Fixes it at the source, and is arguably
   what the union arm meant: a union's *members* are value types. But it changes the checker's
   output types, so it is a gate-moving change and needs the corpus rerun.

Both are real; neither is a one-liner. Recorded rather than attempted, because the rungs behind
it (`if'`, `ifNoElse`) are also behind **narrowing soundness**, which is the bigger of the two
and independent.

## The twelfth stall point — **narrowing soundness**, and it is not a stall so much as unwritten work

`Judge.if'`/`ifNoElse` type their branches at `narrowEnvs κ.classes c Γc` and
`narrowSpine κ.classes c Ic`, so using a branch premise needs `StateOk` at the *narrowed*
environment. Nothing on file establishes that, and `Denote/Sem/State.lean` L52 already says so
("what a proof of `Judge.narrowEnvs`' soundness will have to consume", and `EnvOk`'s identity
conjunct was put there for it).

What it needs, in the order the effort falls:

* Six type-level lemmas — `truthyTy`, `falsyTy`, `isNilTy`, `nonNilTy`, `isATy`, `notATy` —
  each saying the refined type still denotes the value, *given* what the branch tells you
  about it. These are `denM` facts and need no run.

  **Four are done** (clink 56, `Denote/Sem/Narrow.lean`, axiom-clean), and they cost two
  corrections in `Ratchet/Ty.lean`, both in the same direction: *a `.never` catch-all is a
  claim, not a default*. `falsyTy`/`isNilTy` answered `.never` — "this branch cannot run" — at
  the **alias** arm (`.sameAs y ρ` denotes exactly `ρ`, so `.sameAs y .nilT` has a falsy value)
  and at the **nominal** arms (`nil` and `false` descend from `Object`, `Kernel`,
  `BasicObject`, so `falsyTy (.cls "Object") = .never` claims a branch unreachable that a `nil`
  reaches). They refine under the alias and decline to refine nominally now.

  **The other two are `isATy`/`notATy`, and sizing them produced four findings** — §F9, §F10,
  §F11, §F12 in `found-issues.md`, three of them programs `validate` accepted. They are the
  steps in writing the sentence "`isAAnswer`'s answers are true of the heap": the static chain
  is not the machine's chain if a module was `include`d into a core class (§F9); the tested
  *name* need not resolve to the class of that name (§F10); the value's class need not be the
  class its type names, at `.cls` because `rescue` binds a subclass (§F11) and at `.inst`
  because the arm was is-a when it should have been exact (§F12, fixed in the denotation).
  After §F12 the `.inst` case of the lemma is straightforward; the `.cls n` case still needs
  §F9's guard extended from "the chain's own classes" to "the declared classes below `n`".
* **Three run inversions**, one per recognized condition shape: `.var k x` (no dispatch — the
  value *is* `m.getLocal x`, so this one is nearly free), `x.nil?`, and `x.is_a?(C)` / `C === x`
  (which is the same dispatch, sides swapped). The last two need the run of a concrete builtin
  send inverted, which is the same machinery the whole `call*` family needs — so it is not a
  detour but a down payment.
* The `&&` shape (`narrowCond?`'s first arm) is the desugarer's `seq`/`vasgn`/`if'` sandwich
  and is `thenOnly`; it reduces to the `.var` case once the sandwich is stepped through.

## The seventeenth stall point — `Judge.casgn` looked free, and `ConstScopeOk` is what it is not

Measured after §F18 (clink 59). `Judge.casgn` is the rule with **no premise at all** and no
context growth — its conclusion threads `Γ'`/`I'` straight through from its right-hand side —
so it looked like the one remaining rule outside both walls. It is not, and the obstruction is
worth writing down because it is a *component* defect rather than a missing lemma.

`applyKont`'s `.casgnK` arm writes `constSetIn h defmod n v`, i.e. into
`m.currentFrame.defmod`'s own constant table. `ConstScopeOk` says

```
∀ n, constResolveAt m n = constLookup m.heap n
```

and `constLookup` is **only `Object`'s own table** (`RubyCore/Heap.lean` L597). At a machine
standing inside `class A … end` the two sides agree as long as `A` owns no constants — which
is exactly the machine a class body starts from, so such a machine *is* conformant. Writing the
body's first constant makes `constResolveAt m₂ "X"` answer `A`'s new entry while
`constLookup m₂.heap "X"` still answers `none`. So `StateOk` holds before the step and fails
after it, and `SemJudge`'s conclusion asks for it after.

**The component cannot simply be strengthened, because it is on both sides of the implication.**
`ConstScopeOk` is a conjunct of `StateOk κ Γ I m` (hypothesis) *and* of `StateOk κ Γ' I' m'`
(conclusion); what fails is the conclusion, so the fix has to be a **weakening**, and the
obvious weakenings all break the three `.const` rungs that consume it — excluding names a cref
class owns excludes exactly the names those rungs are about, since at `cref = [Object]` the
owning class *is* the toplevel table.

Which is the **eighth stall point** arriving from a new direction: the honest fix is for `Ctx`
to record the cref and for the `.const` rules to be about resolution *at the recorded cref*
rather than at the toplevel. So `casgn`/`cpathAsgn` belong to the declaration-family redesign
after all, and `AGENTS.md`'s "the remaining ladder is two items" survives the audit — with the
list of what is in item (2) two rules longer than it looked.

Not wasted: the attempt is what found **§F18**, which is a reachable soundness bug in the same
rule, and the guard that fixes it (`constAsgnOk`) is what any future version of the rule needs
anyway.

### …and a **third** reason, which is not about where the machine is standing (2026-09-10)

Measured while re-sizing `casgn` after `context-splitting.md` step 5 had removed the "κ is not
threaded" obstruction. The rule now has three independent obstructions, and this is the one the
cref redesign does **not** fix, because it is not about the frame at all.

`constAsgnOk`'s guard (§F18) refuses a rebinding only when the *tables* describe the name — a
recorded constant at a different type, a declared class, a `builtinClsNames` entry, or an
`excName?`. `builtinClsNames` is nine names, and **`Regexp` is not one of them** while
`Judge.regexpLit` concludes `.cls "Regexp"`. Measured:

```
constAsgnOk ctx0 "Regexp" (.cls "String")  =  true      -- permitted
constAsgnOk ctx0 "Comparable" .int         =  true
constAsgnOk ctx0 "Range" .int              =  true
```

`denM (.cls n)` is `isAName`, which resolves `n` through `classNamed?` → `constLookup` → the
toplevel table. So at `Γ = [("r", .cls "Regexp")]` and a conformant machine where `r` holds a
Regexp, the run of `Regexp = "s"` returns and leaves `classNamed? m'.heap "Regexp" = none` —
`EnvOk Γ m'` is false, so **`Obl.Judge.casgn`'s `StateOk κ Γ' I' m'` conjunct is false**, and
no premise of the rule can exclude it.

Not reachable, and that was checked: every other producer of a nominal `Ty` is inside the guard
(`constCls` needs `clsGet?`, `constBuiltin` needs `BuiltinCls`, `constExc` needs `excName?`,
`rescueBind?`'s `.cls n` is an exception class), and rebinding the constant `Regexp` is
behaviourally inert — no `PrimSig` row has a `Regexp` receiver and `/x/` consults no constant.
Written up as `found-issues.md` **§F22**, with the two candidate repairs; the point for this
stall point is that `casgn` needs *both* the cref and one of those, so it is two fixes away
rather than one.

**And the pattern is §F10's, read from the other side.** §F10 was "a narrowing read the
constant's *name*, and a constant is not its name"; this is "an *assignment* to a name falsifies
every type that mentions it, and the set of names a `Ty` can mention is not the set the context
records." Both are the nominal arms being name-keyed against a mutable table, and the second
candidate repair in §F22 — identity-keyed nominal arms, which `Ty.inst`'s `isExactInst` already
half-is — would close both.

## The layer, as built so far (clink 59) — and one correction to its per-step statement

Three files, bottom-up, and the order is `RubyCore/Proof/KontFrame*.lean`'s:

| File | What is proved |
|---|---|
| `Locals.lean` | the capture chain (`ReachesB`), `setLocal`'s target is on it, `CaptureDown` + fuel-irrelevance, `getLocal_congr`, and `Sealed` |
| `FrameLocal.lean` | **the whole `Builtins` layer**: `builtins_run_locals` and the six dispatchers under it |
| `StepLocal.lean` | `LocalsOff` — `LocalsSame` weakened to one frame — and the three leaf closers the interpreter needs |

**The correction.** The per-step claim cannot be stated with `¬ ReachesFrame m b`. Measured on
`unwind`, whose automation closes every arm but the four helper hand-offs, one of which
(`callClosure`) is reached at `{ m with stack := m.stack.tail }`: `ReachesFrame` reads the chain
from `m.stack.headD 0`, so **a stack pop can make `b` reachable again** — which is the end of an
activation, and exactly why `Sealed` quantifies over every frame on the stack. So the claim is

```
Sealed b m → b < m.frames.size → stepFn m = .next m' → LocalsOff b m m' ∧ Sealed b m'
```

and the second conjunct is where the layer stops being automation: each of the six
`frames.push`es needs "the new frame's chain misses `b`" — free for a method frame (`captured =
none`), a *fact about the closure* for a block frame — and each closure allocation needs "the new
closure's captured chain misses `b`". Which is the closure premise the sixteenth stall point
predicted, arriving where it said it would.

Next: `Sealed.pop`/`push_method`/`push_block`/`alloc_closure`, and the `ClosuresOk` exactness
component they are stated against.

## The sixteenth stall point — the fifteenth's plan names a theorem that is **false**

Measured while starting the layer (clink 59, after `Judge.ivarAsgn`). The fifteenth stall point
below says the locals half needs

> a callee's run leaves the caller's frame's locals alone

and **that statement is not true of the semantics.** The witness is three lines of ordinary
Ruby:

```ruby
x = 1
f = lambda { x = 2 }
def g(p); p.call; end
g(f)                      # x is 2
```

`g`'s activation writes `x`, a local of `g`'s *caller's* frame. It can, because
`Machine.setLocal` walks the **capture chain** rather than the frame stack, and `f`'s closure
captured the caller's frame. Nothing about being inside a callee prevents reaching it: the
callee only needs to get its hands on a closure that captured it, and an argument, an ivar, a
constant or a global will all carry one.

So the layer cannot be built as planned. What *is* true has to name the closures:

> a run leaves frame `b`'s locals alone **provided no closure the run can reach captures a
> frame whose chain contains `b`**

and that is a claim about the heap, not about syntax — which means the syntactic premise
(`noLocalAsgn`) cannot imply it on its own, at any tightening. Three consequences, in the
order they bite:

1. **`found-issues.md` §F13 is not fixable by tightening `noLocalAsgn`'s grammar.** Every
   tightening still admits a `.send`, and `x && x > 1` (rung 132, `narrow-and-guard`) is the
   program the feature exists for, so `.send` cannot be dropped: three rung derivations
   (132 plus `begin'`'s two, 192/194) stop compiling if it is, which the 177/177 gate forbids.
   Measured by making the send arm answer `false` and rebuilding.
2. **Pinning the dispatch to a builtin does not work either**, and this was measured rather
   than assumed. A `StateOk` component of the `QueryOk` family — "at every class this name
   resolves to a builtin" — is *false at the booted heap* for every operator the rungs need
   except `nil?` and `length`: `>`/`<`/`>=`/`<=` resolve to a **prelude** `Comparable` method
   at `Symbol`, `Numeric` and `Pathname`, `==` at `Numeric`/`Pathname`/`Encoding`, `!=` at
   *every* class, `empty?` at `Pathname`, `size` at `Range`. A prelude body is arbitrary Ruby
   and dispatches `<=>` onward, so the builtin route collapses back into the general case.
3. **The honest premise bounds the program's closures, not its expressions.** `Ctx.closures`
   is already the checker's closure table, and `StateOk`'s `ClosuresOk` is currently `trivial`
   — so the shape of the fix is an **exactness** component in `MethodsExact`'s mould ("every
   closure in the heap is one `κ` records, or the prelude's") plus a syntactic premise over
   that table ("no closure assigns a local it captures"). Rungs 132/192/194 have no closures at
   all, so it should be corpus-neutral; §F13's own witness (corpus 248) is refused for the
   right reason under it.

The exactness component is the part with a cost that has not been paid anywhere yet: unlike
`MethodsExact`, whose upper bound is measured once at the booted heap and grown by
`declaresName`, closures are created **at run time** by `lambdaLit`/`iterBlock`, so the
component has to be preserved by rules that allocate them — and `Judge.lambdaLit` is already
discharged, which means it gets re-proved. That is expected (the procedure above: a rung that
will not close is information about a `StateOk` component), and it is worth knowing before
starting rather than during.

## The eighteenth stall point — **the seal is not inductive**, and one builtin is why

Measured in clink 60, by attempting the step the layer's own plan names next: carry `Sealed b`
across `Builtins.run`. `Denote/Sem/FrameLocal.lean` had already proved that layer uniform for
`LocalsSame`, and the seal reads `captured` rather than `locals`, so this looked like the free
half. It is false, and there is exactly one falsifier in the whole builtin table.

`Symbol#to_proc` (`RubyCore/Builtins/Strings.lean` L441) **allocates a closure**:

```lean
let cl : Closure :=
  { params := [.req "__recv", .rest (some "__rest")], locals := [],
    body := .send (some (.var .lvar "__recv")) s [.splat (some (.var .lvar "__rest"))] none,
    captured := 0, home := 0, lam := true }
```

`captured := 0` — the **toplevel frame** — because `Closure.captured` is a `FrameId` and not an
`Option FrameId`, so there is no way to spell "captures nothing" and `0` is the inert choice.
`Sealed`'s `clos` clause reads exactly that field, so the allocation drops a closure over frame
`0` into the heap and the seal at `b = 0` is gone. `Denote/Sem/StepLocal.lean`'s
**`not_BuiltinsSeal`** is the refutation, at the smallest machine where the seal says anything
(two frames, neither capturing, the caller `0` sealed off behind the frame that is running, an
empty heap), conditional on one `#guard`ed `Bool` for `Denote/Sanity.lean`'s reason.

`b = 0` is not an edge case. It is the **toplevel frame**, which is the frame every toplevel
narrowing rung is about.

Three things follow, and the third is the design consequence.

1. **It is not a soundness bug in the model.** The closure's body is `__recv.s(*__rest)` — a
   fixed, assignment-free expression — so invoking it cannot write a local of frame `0`.
   `Sealed` is a *sufficient* condition for "`b`'s locals are stable", and this is a place where
   it is strictly stronger than the truth.
2. **It is not repairable by strengthening `Sealed.alloc`.** The allocation really happens, at a
   machine the seal really holds at, so no premise stated over `(b, m)` can exclude it. What
   distinguishes the `to_proc` closure from a dangerous one is its **body**.
3. **So the frame graph is not enough, and the closure clause is not the only one that moves.**
   Admitting an escape (`… ∨ this closure cannot write`) in `Sealed.clos` is the easy half. The
   hard half is that `Sealed.stack` then breaks: `callClosure` pushes a **block frame** whose
   `captured` is the inert closure's, so a frame on the stack now does reach `b`, and the stack
   clause is unconditional. Weakening *it* the same way needs "the code running in that frame
   cannot write", which is a property of `ctl`/`kont` — not of `frames`.

Which is the fifteenth stall point's own prediction arriving with a number on it: the invariant
has to be **joint over the frame graph and the control state** (`LocalStable m x` lifted from an
expression to a whole machine), not a predicate on `frames` alone. `Sealed` is the frame-graph
half and it is built; what is missing is the half that says what the machine is *about to do*.

Two consequences for the next attempt:

* **`ClosuresOk` needs a third escape.** The sixteenth stall point sized the exactness component
  as "every closure in the heap is one `κ` records, or the prelude's". `Symbol#to_proc`'s is
  neither: it is created at run time by a **builtin**, from source that is not in the program
  and not in the prelude. Grep says it is the only one (`RubyCore/Builtins/` has exactly one
  `.proc` allocation), so the escape is a fixed shape rather than an open set — but it has to be
  written down, and it would not have been predicted from the plan.
* **The measurement order was wrong, and cheaply so.** The `Builtins` layer was proved uniform
  for `LocalsSame` (532 lines, clink 59) before anything checked whether the *seal* travelled
  across it. Stating `BuiltinsSeal` as a named `Prop` first would have cost an hour and found
  this. Same lesson as `KontFrame`, and the second time it has paid: **write the layer's target
  down as a `def` before proving the layer under it.**

### Probed against CRuby (2026-09-08) — and the diagnosis above is **too pessimistic**

The section above concludes "the frame graph is not enough" and hands the layer a redesign. A
20-program probe corpus replayed under `--sut lean`, plus CRuby-only probes for what the model
cannot express, says the blocker is smaller than that and sits **in the model, not in the
invariant**. Recorded in `../../found-issues.md` §A6.

**CRuby's `Symbol#to_proc` proc has no binding at all** — `:upcase.to_proc.binding` raises
`ArgumentError` (C-level Proc), `source_location` is `nil`. So `captured := 0` is not "the inert
choice" in a semantically neutral sense; it is an **edge the reference semantics does not have**,
forced by `Closure.captured : Nat` (`RubyCore/Heap.lean:136`) where `Frame.captured` is already
`Option FrameId` (`RubyCore/Machine.lean:57`). `Sealed.clos` reads exactly that field.

That reframes the repair. This file rejected touching the model on "the denotation should not
edit the machine to make itself provable" grounds — and that reasoning does not survive the
measurement: giving `Closure.captured` the `Option` its `Frame` counterpart already has is a
**fidelity fix, justified independently of any proof**, and it happens to make `Sealed.alloc`'s
premise dischargeable at both sites. Blast radius measured: 2 construction sites, ~4 readers
under `RubyCore/Interp/`, 14 files under `RubyCore/Proof/`, 12 under `../`.

**Two corrections to the section above, both from the probes:**

* **There are two spurious-edge sites, not one.** `grep 'captured := 0'` over the whole model
  finds `Builtins/Strings.lean:449` (`Symbol#to_proc`) **and**
  `Interp/Support.lean:448` (`coerceToProc`, the `&:sym` block-pass path). The section's
  "grep says it is the only one" was scoped to `Builtins/`; the interpreter layer creates the
  same fiction, so the problem recurs at the next layer of the walk rather than being confined
  to the one below it.
* **The inertness escape is not needed**, and with it goes the `Sealed.stack` objection that
  made this look like a redesign. That objection was a consequence of admitting inert closures
  in `clos`; if the edge simply is not created, nothing pushes a block frame over `b` and the
  unconditional `stack` clause is fine.

**What the probes do *not* say.** They remove the known counterexample; they do not establish
that `Sealed` is inductive. `not_BuiltinsSeal` remains valid as a statement about the model as
it stands today — it is a theorem about `Sealed` and `Builtins.run`, both definitions in this
repo, and no amount of CRuby fidelity bears on its truth. What changes is the *prognosis*: the
next attempt should try the `Option` first and re-attempt the `Builtins` layer, rather than
starting from a joint frame-graph/control-state invariant.

**And the seal is guarding something real**, which was worth checking rather than assuming. The
sixteenth stall point's witness reproduces on both executors — `x = 1; f = lambda { x = 2 };
def g(p); p.call; end; g(f); x` is `2` under CRuby *and* under the model — while the same shape
with a `to_proc` proc leaves `x` at `1` on both. So the hazard `Sealed` exists for is genuine
and `Symbol#to_proc` is not an instance of it.

### Would the `Option` make `Sealed` inductive? **Not on its own — it needs a third clause** (2026-09-08)

Asked immediately after the probes, and answered by enumerating every writer of the two things
`Sealed` reads rather than by argument. The model is small enough for this to be exhaustive.

**Clause `clos` — every allocation of a `.proc` payload. There are exactly three:**

| site | `captured` | after the `Option` fix |
|---|---|---|
| `reifyBlock`, `Interp/Support.lean:427` | `cur = m.stack.headD 0` | **free already** — `cur` is the current frame, which `FramesWF.nonEmpty` puts on the stack, so `Sealed.stack` at `cur` discharges `Sealed.alloc`'s premise |
| `coerceToProc` (`&:sym`), `Interp/Support.lean:448` | `0` (the fiction) | `none` — free |
| `Symbol#to_proc`, `Builtins/Strings.lean:449` | `0` (the fiction) | `none` — free |

So the closure half **does** close, and the load-bearing observation is the first row rather
than the fix: a user block captures the frame it is created in, and that frame is on the stack,
so the seal pays for its own closures.

**Clause `stack` — every `frames.push`. There are six**, and four push a frame whose `captured`
is defaulted (`Dispatch.lean:229`, `284`, `403`, `Kont.lean:115` — class bodies and ordinary
method frames), so they are free. The two that set it:

| site | `captured` from | covered by |
|---|---|---|
| `callClosure`, `Interp/Support.lean:533` | `some cl.captured`, `cl` a `Closure` read from the heap | `Sealed.clos` — this is what that clause is *for* |
| `enterUserMethod`, `Interp/Dispatch.lean:154` | `md.capturedFrame`, `md` a **`MethodDef`** read from the heap | **nothing in `Sealed`** |

**`MethodDef.capturedFrame` is a second capture graph, and `Sealed` does not mention it.**
`define_method` installs a method whose body sees the defining scope's locals
(`Heap.lean:83`; set at `Reflect.lean:233`), and entering that method pushes a frame with
`captured := md.capturedFrame`. So the sixteenth stall point's hazard has a second route,
through a *method* rather than a proc — probed on both executors, agreeing:

```ruby
x = 1
Object.send(:define_method, :setx) { x = 2 }
def g; setx; end
g
x                       # CRuby: 2   model: 2
```

**But the third clause is closed, which is the whole question.** `reflectDefineMethod` sets
`capturedFrame := some cl.captured` where `cl` comes from `procClosure? m bv` — a closure
**already in the heap** — so `Sealed.clos` at that closure discharges the new clause exactly, in
the same way `clos` discharges `callClosure`'s push. Every other `MethodDef` writer is either a
fresh literal that defaults `capturedFrame := none` (ordinary `def` `Interp.lean:270`,
`def self.m` `Interp.lean:377` / `Kont.lean:103`, the `attr_*` accessors `Dispatch.lean:582`/
`585`, the undef stub `Heap.lean:666`) or a `{ md with … }` copy of a method already installed
(`Reflect.lean:98`/`105`, `alias` `Interp.lean:311` / `Reflect.lean:499`), which inherits a
`capturedFrame` the clause already covers. **J33's capture erasure helps too**: a `localFreeB`
body is installed with `capturedFrame := none`, so the clause is vacuous for every
`define_method` whose body reads no local.

**Verdict.** `Sealed` + the `Option` + a clause over installed `MethodDef`s is **three clauses
that discharge each other**, with no writer left over. That is a materially better position than
the joint frame-graph/control-state invariant this stall point first called for — the control
state does not have to enter after all.

Three honest caveats, because this is an enumeration of *writers* and not a proof:

* It establishes that **no arm is blocked in principle**. The per-arm walk over `stepFn` — the
  thing `FrameLocal.lean` did for `LocalsSame` — is still the work.
* The new clause needs the "installed anywhere in the heap" quantifier, which is
  `MethodsExact`'s shape (`Denote/Sem/Frame.lean`), and like it should be **measured at the
  booted machine** before it is written down — the prelude is a large body of installed methods
  and `Denote/Sanity.lean` is where that check belongs.
* The `Option` change ripples into `md.capturedFrame := cl.captured` (no longer `some`), and it
  changes the *machine*, so the difftest and all 47 rungs need re-verification.

### The decision (2026-09-08): **`Closure.captured` becomes an `Option`, and the `:sym.to_proc` sites take `none`**

> **DONE (2026-09-08, L266).** Implemented exactly as decided below, with three departures
> worth reading before trusting the table: the field is `Option Nat` and not `Option FrameId`
> (the same import-cycle dodge `MethodDef.capturedFrame` already makes, and the docstring now
> says so in one place instead of two); Lean's `Option` coercion means every *construction*
> site that wrote a bare `FrameId` — `blockClosure`, `lamClos`, `dmPcl` — still elaborates
> untouched, so the ripple was smaller than the eight-site count suggested and the sites that
> actually broke were the *reads*; and two definitions changed shape rather than being
> re-parenthesised, which is where the fidelity actually moved:
>
> * `Sealed.clos` and `FramesWF.clos` are now quantified — `∀ p, cl.captured = some p → …` —
>   matching the shape their `Frame` clauses already had. A capture-free closure discharges
>   them **vacuously** instead of being a claim about frame `0`. This is the repair.
> * `Denote/Apply.lean`'s `closLocal` goes through a new `frameLocal?`, which answers `.nil`
>   for `none`. `getD 0` would have been wrong here and nowhere else: `callClosure` pushes the
>   block frame with `captured := none`, so the *body's* walk stops at its own activation,
>   and a denotation reading frame `0`'s locals would have described a program the machine
>   does not run. `closSelf` **does** take `getD 0`, because `callClosure` does.
>
> `Denote/Sem/StepLocal.lean`'s `not_BuiltinsSeal` is **retired**: `toProcBreaksB` is replaced
> by `toProcSealsB` (`#guard`ed, and non-vacuous — it checks the call returns a Proc *and*
> that the Proc captures nothing). `BuiltinsSeal` is left stated and unproved on purpose; one
> builtin measured is not the layer walked.
>
> Re-verified, all green: difftest tier 0 **1304 ran / 992 agree / 0 disagree**; corpus
> agreement **254/254**; `checkrungs` **177/177 + 145/145**; `run_ratchet.sh` **178/254**
> (unmoved); `semladder` **47/83** with the denominator still 83; `lake build` clean in both
> packages, no `sorry`, axioms a subset of `propext`/`Classical.choice`/`Quot.sound`.
>
> **Not done, and not attributable to this change:** `lake build Metatheory` is red at HEAD
> and stayed red — three pre-existing breaks, listed in `../found-issues.md` §A7. Every
> `Option` ripple *inside* `Metatheory` was fixed and verified (by transiently `sorry`ing
> exactly those three and building the whole closure, then reverting), so the library is no
> worse than it was found.

Taken deliberately rather than derived, so the reasoning is recorded here with the alternative
that was turned down.

**What changes.** `Closure.captured : Nat` → `Option FrameId`, matching `Frame.captured`, which
has been an `Option` all along. Eight sites in the model proper:

| site | now | after |
|---|---|---|
| `RubyCore/Heap.lean:136` | `captured : Nat` | `captured : Option FrameId` |
| `Interp/Support.lean:427` (`reifyBlock`) | `captured := cur` | `captured := some cur` |
| `Interp/Support.lean:448` (`coerceToProc`, `&:sym`) | `captured := 0` | **`captured := none`** |
| `Builtins/Strings.lean:449` (`Symbol#to_proc`) | `captured := 0` | **`captured := none`** |
| `Interp/Support.lean:525` (`callClosure`) | `m.frames.getD cl.captured default` | `m.frames.getD (cl.captured.getD 0) default` |
| `Interp/Support.lean:533` (`callClosure`) | `captured := some cl.captured` | `captured := cl.captured` |
| `Interp/Reflect.lean:223` | `(m.frames.getD cl.captured default).cref` | `.getD (cl.captured.getD 0)` |
| `Interp/Reflect.lean:237` | `else some cl.captured` | `else cl.captured` |

plus the statements that mention `cl.captured` in `RubyCore/Proof/Static/{Konts,Locals,Iter,
LambdaArrow}.lean` and in `../Apply.lean`, `../Local.lean`, `../Ext.lean`, `Locals.lean`.

**Why it is behaviour-preserving at the two `none` sites, and why the `.getD 0` is not a
cheat.** The `getD 0` keeps `callClosure` reading exactly the frame it reads today for these
closures — frame `0`'s `self`/`defmod`/`blk`/`cref`. What *does* change is the pushed block
frame's own `captured`, which becomes `none`: the chain stops at the block frame instead of
continuing into the toplevel. Unobservable, because the body's only free names are its own
parameters (`__recv`, `__rest`), so nothing walks the chain — and it is the **more faithful**
reading, since CRuby's object has no binding at all (`found-issues.md` §A6a).

**Tracking item — this is not a general fix, and it should not be read as one.** It is right
for exactly the two sites where the model *invents* a Proc for a Symbol. The moment `&obj`
dispatches a **user-defined `to_proc`** — today `coerceToProc` gates it ("block-pass of a
non-Proc (to_proc dispatch is L2)") — the returned Proc is an ordinary closure created by
`reifyBlock` at a real frame, and it will capture, and `Sealed.clos` will have to carry it
exactly as it carries every other user closure. Nothing here breaks then; the point is that
nothing here *helps* then either. **We are explicitly not solving that now.** When L2 lands,
re-read this subsection before assuming the seal still closes.

**Rejected: prove the seal survives by reducing `Symbol#to_proc` and showing it mutates
nothing.** The alternative was to leave `captured := 0` in place and discharge the allocation
with a lemma — unfold the arm, look at the closure it builds, observe that its body
(`__recv.s(*__rest)`) can write no local of whatever frame it names, and conclude the seal is
undisturbed. Turned down for four reasons, in the order they matter:

1. **It does not discharge `Sealed` as stated.** `Sealed.clos` is a claim about the capture
   *graph* — "no closure in the heap reaches `b`" — and the lemma would prove something about
   what one closure *does*. To spend it you first have to weaken the clause to `… ∨ this
   closure is inert`, and that escape is what drags `Sealed.stack` in after it (item 3 of this
   stall point): `callClosure` pushes a block frame over `b` from an inert closure, the stack
   clause is unconditional, and repairing *it* needs a predicate on `ctl`/`kont`. The lemma is
   not the fix; it only buys the escape, and the escape is the expensive half.
2. **It does not generalise.** The argument is about one fixed body. It says nothing about the
   user-defined `to_proc` above, so the tracking item would come due with no machinery in hand.
3. **It leaves the fidelity gap standing.** The model would keep a capture edge CRuby does not
   have, and every future proof about the capture graph would pay for it again — the same
   `Denote`-pays-for-the-model's-fiction trade, one more time.
4. **The cost is the wrong way round.** The `Option` is eight sites and a mechanical ripple; the
   inertness route is a new syntactic predicate, a weakened `clos`, a control-keyed `stack`, and
   a per-arm walk that has to preserve both.

The one thing the rejected route had going for it: it touches no `RubyCore/` definition, so it
costs no difftest re-run. That is real and it is not enough — the `Option` re-run is a
one-time cost and the fiction is permanent.

### Draft: the **`MethodDef` arm** of `Sealed`

> **BUILT (2026-09-08, L267).** `Sealed.meth` and its `FramesWF.meth` twin are in
> `Denote/Sem/Locals.lean`, stated through a named `methodIn` lookup, and threaded through all
> eleven preservation lemmas. Two departures from the draft:
> * **`Sealed.alloc`/`FramesWF.alloc` grew a second premise.** The draft's writer-by-writer
>   argument is about `defineMethod` writing into an *existing* payload; a fresh `Heap.alloc`
>   of a **class** object carries a method table too, and the clause owes it the same thing
>   `clos` owes for a fresh Proc. Every caller in the model discharges it trivially (classes
>   are allocated with `methods := []`) but the premise has to be there for the lemma to be
>   true, and it was not in the draft.
> * The lookup is named (`methodIn h k n`) rather than written inline three times, because
>   the clause, its twin and their consumers all have to agree on it syntactically.
>
> Vacuity re-measured after the change (`probes/measure_captures.lean`): still **0** capturing
> methods and **0** Procs at the booted machine, so `meth` and `clos` are both satisfiable and
> trivially satisfied where the ladder starts.
>
> **`Sealed` is now the closed three-clause invariant the enumeration predicted** — stack,
> closures, methods, with no writer left over and the control state not in it.

The third clause the enumeration above says is missing. Written out here so the next session
implements rather than re-derives it.

```lean
structure Sealed (b : FrameId) (m : Machine) : Prop where
  /-- No frame on the activation stack reaches `b`. -/
  stack : ∀ fid ∈ m.stack, ReachesB m b fid (m.frames.size + 1) = false
  /-- …no closure in the heap captured a chain through `b`… -/
  clos : ∀ (o : ObjId) (cl : Closure), procClosure? m.heap (.ref o) = some cl →
    ∀ p, cl.captured = some p → ReachesB m b p (m.frames.size + 1) = false
  /-- …and no **method** in the heap did either. `define_method` installs a body that sees the
      defining scope's locals (`MethodDef.capturedFrame`, `RubyCore/Heap.lean:83`), and
      `enterUserMethod` pushes a frame with `captured := md.capturedFrame` — so a method is a
      second capture graph, and the seal has to read it too. -/
  meth : ∀ (k : ObjId) (n : String) (md : MethodDef),
    (m.heap.classPayload? k).bind
      (fun cp => (cp.methods.find? (·.1 == n)).map (·.2)) = some md →
    ∀ p, md.capturedFrame = some p → ReachesB m b p (m.frames.size + 1) = false
```

with the in-range twin on `FramesWF`, mirroring its `clos` clause:

```lean
  meth : ∀ k n md, <same lookup> = some md → ∀ p, md.capturedFrame = some p →
    p < m.frames.size
```

**What consumes it:** `Sealed.push` at `enterUserMethod` (`Interp/Dispatch.lean:154`), which is
the one frame push the two existing clauses do not cover.

**What re-establishes it, writer by writer** (the enumeration above is the argument that this
list is complete):

* `reflectDefineMethod` (`Interp/Reflect.lean:233`) sets `capturedFrame` from `procClosure? m
  bv` — a closure **already in the heap** — so `Sealed.clos` at that closure discharges it, the
  same shape in which `clos` discharges `callClosure`'s push. This is the only writer that can
  make the clause non-trivial.
* Fresh literals that default the field to `none`: ordinary `def` (`Interp.lean:270`),
  `def self.m` (`Interp.lean:377`, `Interp/Kont.lean:103`), the `attr_*` accessors
  (`Interp/Dispatch.lean:582`/`585`), the undef stub (`Heap.lean:666`).
* `{ md with … }` copies of an already-installed method, which inherit a `capturedFrame` the
  clause already covers: visibility and `module_function` (`Interp/Reflect.lean:98`/`105`),
  `alias` (`Interp.lean:311`, `Interp/Reflect.lean:499`).
* **J33's capture erasure** makes it vacuous for free wherever it applies: a `localFreeB` body
  is installed with `capturedFrame := none`.

**Measured before writing it down**, which is `../Sanity.lean`'s rule and the reason the eighth
and tenth stall points exist. At the booted machine (`probes/measure_captures.lean`):

```
methods with a capturedFrame : 0
Proc objects in the heap     : 0
frames.size                  : 71     (dead activations; the stack is [0])
```

So both the new clause and the existing `clos` clause are **vacuous at the machine the ladder
starts from** — the prelude installs no capturing method and leaves no Proc behind. Adding the
arm therefore costs no vacuity risk, which was the thing worth checking: a component that is
unsatisfiable makes every obligation true for the wrong reason, and this one is satisfiable and
trivially so.

**The hazard it excludes is real**, probed on both executors:

```ruby
x = 1
Object.send(:define_method, :setx) { x = 2 }
def g; setx; end
g
x                        # CRuby: 2   model: 2
```

## The fifteenth stall point — **syntax-directed run invariants**, and it is now the largest piece

Named in clink 57, and it is the *merge* of two findings that turned out to be one thing. Both
say: a `Judge` rule relies on a syntactic property of an expression implying a property of its
**run**, and nothing on file relates the two.

* **No return jump** (the fourteenth stall point below): `.ret`/`.brk`/`.nxt` have no `Judge`
  rule, so no derivable expression contains one — therefore a callee body's run cannot escape
  with a return jump, and `SemJudge`'s silence about jumps is harmless. Needed by every rule in
  the call family.
* **Locals preserved** (`found-issues.md` §F13): `narrowCond?`'s `&&` arm licenses a refinement
  when the right-hand side passes `noLocalAsgn`, and the refinement is a claim about the local
  *at the point the branch begins* — so what is needed is that evaluating the right-hand side
  cannot rebind it. Needed by `Judge.if'`/`ifNoElse`, which are otherwise ready: all six
  type-level lemmas are proved (clink 57).

The shape of the fix is the same for both: **one induction over `stepFn` that carries a
syntactic predicate through the machine.** The machine's `ctl` holds an expression and its
`kont` holds continuations that hold expressions, so the predicate has to be lifted from an
expression to a whole machine (`JumpFree m`, `LocalStable m x`) and shown preserved by every
step — which is the same *kind* of walk `RubyCore/Proof/KontFrame*.lean` already does for the
frame property, and the same size.

Two things make it cheaper than the frame layer was. The frame layer had to prove an
*equation* about every helper (`pushK K` commutes with each), while these are **invariants**:
each arm has to show a predicate survives, which `simp` closes far more often. And the
`Builtins` layer is transparent for both — a builtin cannot introduce Ruby syntax, so
`Builtins.run` needs one lemma rather than 121.

### And one thing makes it *not* three pieces but one (clink 58)

Measured while looking for a cheaper route to `Judge.if'`: the locals half and the call
decomposition are **entangled**, so they cannot be sequenced.

The locals claim would like to be an induction on the *expression* — `noLocalAsgn`'s grammar is
small (literals, reads, `const`, `self`, sends, arrays, `if`, `seq`), and every arm but one is
a bounded number of `stepFn` steps that visibly touch no local. The exception is `.send`, which
`noLocalAsgn` **must** admit (`x && x > 1` is the shape the feature exists for) and which may
dispatch a *user method*: its run pushes a frame, runs an arbitrary body, and pops. So the
expression induction needs

> a callee's run leaves the caller's frame's locals alone

which is a **run**-level statement about the activation between a `frameK` push and its pop —
i.e. the same decomposition the call family needs, and the one that needs jump-freeness to
state (a body may `return`). Each half of the wall needs the other.

The consequence for planning: there is no useful smaller first step. The layer is
`frameK`-decomposition + jump-freeness + the two syntactic invariants, built together, and the
2 narrowing rungs (`if'`/`ifNoElse`) plus the ~21 call rungs come out at the end of it rather
than in stages. That is worth knowing before starting it, and it is why clink 58 stopped at the
*guards* (`JudgeSeq.guard`/`nextGuard`), which are the two narrowing consumers that read only
the else side and therefore need none of it.

Until it lands, the honest statement of the ladder's remaining shape is: **43 of 83 discharged,
~17 more sitting behind this one wall**, and the rest behind the judgment redesign the
declaration family needs (§the seventh/eighth stall points).

## The fourteenth stall point — **`SemJudge` is too weak for a rule whose premise is a body**

Found while sizing `Judge.callMethod` (clink 56), and it has to land before *any* call rung.

`Obl.Judge.callMethod` takes `SemJudge κ' Γb d.body ρ Γb' Iout` and has to conclude something
about the call's value. For `d.body = return "s"` that premise holds **vacuously**: the run of
`.ret e` jumps, so `Evals` is never satisfied, so the implication is empty — while the machine
really runs that body (`ClassesOk`: `md.body = toRuby d.body`) and the call really returns a
String. So the obligation is *false*, at `ρ = .int`, for a body no rung would ever write.

The syntactic judgment is safe, and the reason is worth stating precisely: `.ret`, `.brk` and
`.nxt` have **no `Judge` rule at all**, so no derivable expression contains one — the single
exception being `bodyResult`, which matches a lambda body that *is* `return e` and judges `e`,
outside the judgment. `Judge` therefore implies jump-freeness **structurally**, exactly as it
implied `Plain`-ness structurally (§the fifth stall point's `Plain`, clink 54), and `SemJudge`
does not.

So the fix is the same one: a **jump-freeness conjunct** on `SemJudge`, `SemJudgeAll` and
friends, discharged per rung from the conclusion's shape plus the premises' own conjuncts. The
cost is one edit per rung on file (42) and it is mechanical; the alternative — a `Returns`-style
conjunct that says what the run does when it *does* jump — is strictly more work and buys
nothing until a rule types a `return`.

Two things worth checking when it lands: whether `Plain` should simply become recursive and
absorb it (the conjuncts are the same species — "this syntax is not what it looks like"), and
whether `closCall`'s `bodyResult` shape needs an exception (its judged expression is `e`, not
the `.ret`, so probably not).

## The thirteenth stall point — **the dispatch chain**, and it is the biggest of the four

After clink 54 the remaining 45 rules sit behind exactly four things. Three are above; this is
the fourth, and it is what the table's row "the call lemma — unwritten" turns into once the
argument walk exists.

`Denote/Sem/Send.lean` takes a call's run apart down to `finishSend`. From there the chain is

```
finishSend … .none  =  invoke …                       -- `rfl`
invoke …            →  invoke.invokeDispatch …        -- one `match` on the receiver's payload
invokeDispatch …    →  lookup m.heap recv mname       -- the ancestor walk
                    →  Builtins.run bid recv args m   -- the builtin
```

and the two ends are what is missing:

* **The lookup needs a heap fact `StateOk` does not have.** `MethodsExact`/`ClassesOk`/`DefsOk`
  describe the classes the *context* knows; a builtin like `Object#is_a?` is a boot binding,
  and nothing says it is intact. A program may reopen `Integer` and redefine `is_a?` — which
  is exactly what `corpus/241-reopen-integer-is-a-unsafe` probes (the checker rejects it, so
  the gap is not reachable, but the *obligation* still quantifies over machines that have it).
  So this wants a component in the shape of `CoreOk`: the boot bindings the rules dispatch on,
  with a satisfiability witness at `bootMachine`.

  **Two wrinkles found while sizing it, both of which constrain the shape.** First, the naive
  "the lookup finds the boot builtin" is **false at a dangling reference**: `Heap.get` answers
  `default`, whose `klass` is `0`, so `classOf` gives a class whose ancestry does not reach
  `Object` and the lookup misses. So the existence half has to be conditioned — on
  `Boot.objectId ∈ ancestors m.heap (classOf m.heap recv)`, or on the receiver's *type* via
  `expectedClasses` — while the "whatever it finds is the boot builtin" half can stay
  unconditional. Second, the *miss* branch is not free: `dispatchMiss` routes to a user
  `method_missing`, which can return anything, so a rule that reasons from the dispatch also
  needs §F4's `nameFree κ "method_missing"` premise or the equivalent. The tempting shortcut —
  a component that asserts *the dispatch answers a boolean* — is not conformance but the rule's
  own conclusion moved into `StateOk`, and must not be taken (`AGENTS.md` §Justification).
* **The builtin needs its signature honoured**, which for `Judge.prim`/`callAsm` means one
  conformance fact **per `PrimSig` row** — the "list of named builtins" that
  `../../type-safety-by-reachability.md` §9.0/§10.3 already calls the remaining model-coverage
  job. `RubyCore/Proof/BuiltinConformance.lean` has the shape for four `Integer` rows
  (`int_add_dispatch` and friends, over an `IntBuiltinResolves` hypothesis); the table has
  order-of-200 rows.

**The cheap end of it is worth doing first.** `Judge.isAQuery` and `caseEqQuery` conclude
`Ty.bool`, so they need only *the result is a boolean* — no signature table at all, just the
lookup fact and one `Builtins.run` unfolding. `classOf`/`clsToS` are the same shape one row
over. That is four rungs for the first component, and the component is then reusable for the
twelfth stall point's `x.is_a?(C)` inversion, which narrowing needs anyway.

### The cheap end, **done** (clinks 54–55) — and what it cost that this estimate did not name

Three of the four: `isAQuery`, `caseEqQuery`, `clsToS`. (`classOf` is not the fourth; it is
`found-issues.md` §F8 — its conclusion is *exact* where its receiver premise is an is-a test.)
The estimate above was right about the shape and named the two wrinkles correctly; two things
it did not predict:

* **The component cannot always be indexed by the receiver's class.** `QueryOk`'s shape works
  for `is_a?` because *every* class in the boot heap resolves it to `Object#is_a?` (measured:
  0 exceptions of 105). `===` and `to_s` are not like that — 43 and 63 exceptions
  respectively — but they are clean at exactly the receiver shape their rules allow, a **class
  object**, where the walk starts at the eigenclass. Hence `ClsQueryOk`, indexed by the object
  and conditioned on its class payload. Any further row should be measured *both* ways before
  a shape is chosen; the measurement is a dozen lines of `#eval` over `bootMachine.heap`.
* **A `.clsOf` receiver premise needs a transport, and it is not a component.** The receiver is
  evaluated before the arguments, so its class-ness is established at one machine and read at
  another. This is the same *kind* of gap as the seventh stall point's remnant below, but
  unlike that one it is **true** and cheap: class-ness, unlike an array's element types, is
  monotone. `SemJudge`'s first conjunct is now `Framed` (see its docstring), carrying it
  alongside frame balance, discharged per-rule and composed by `Framed.trans`. Every remaining
  rule in the call family with a `.clsOf` premise — `newInst`, `newInstNoInit`, the `smroGet?`
  dispatches — inherits it.

What is left of this stall point is therefore the **expensive** end only, unchanged and
correctly sized above: `Judge.prim`/`callAsm` and the ~200 `PrimSig` rows. One refinement to
its shape, from the measurements here: a row needs **two** facts, not one — which class binds
the name to which bid (receiver-*dependent*, so it cannot be a `nameFree`-guarded list the way
`QueryOk` is) and what that bid answers.

## The seventh stall point's remnant, measured — and it is a **falsity**, not a gap

The table above says what is left of the seventh is "the *transport* a consumer needs to move
an argument's type to the call machine". Attempted at `Judge.arrayLit` (clink 54), that
transport is **false**, and the counterexample is the same one clink 53 was avoiding:

`denM`'s `.arrayOf` arm reads the elements at the machine it is given, so
`Judge.arrayLit`'s conclusion — `denM ((elemTy τs).arrayOf) m' arr` at the machine the *whole*
literal ended at — asks for every element to be in the element type **there**. `DenAllAt` says
each element is in its type at the machine *its own* evaluation ended at, deliberately. A later
element that mutates an earlier one's ivars separates the two:

```ruby
o = C.new                                   # o : inst C (@a : Int)
xs = [o, o.instance_variable_set(:@a, "s")] # the second element makes the first's type false
xs[0].get + 1                               # certified Integer + Integer; runs String + Integer
```

`corpus/242-array-lit-element-mutated-unsafe` is that program, and the checker **rejects** it —
`instance_variable_set` is not typed — so like §F5, the eleventh stall point and
`240`/`241`, the rule is unsound in isolation and its soundness in the checker rests on an
unstated invariant. The same argument applies verbatim to `hashLit` and to every `DenAllAt`
consumer that reads its elements at the final machine.

What a fix would have to choose between: **restate the consumers** so they read each element at
its own machine (which `Ty.arrayOf` cannot express — the type has one machine, not one per
element), or **add a premise** that no argument mutates (a purity condition, which is a real
restriction), or **weaken `denM`'s `.arrayOf` arm** to quantify over `Later`-futures the way the
arrow arms do (which is what made `strLit` work in clink 45, and is the direction that has
precedent). None is a one-liner, and none is on the critical path while the reachable set does
not exercise it.


## The `Builtins` layer, half proved — and the other half specified (L267)

The eighteenth stall point's refutation is gone (L266) and `Sealed` is closed (L267's
`MethodDef` arm), so `BuiltinsSeal` is attemptable again. It is now **half done**, and the
half that is done was nearly free.

**What the invariants read.** `Sealed` and `FramesWF` read exactly two things: the *frames'*
`captured` links (plus, for the congruence, the frame count), and the *heap's* closures and
methods. That is a clean split, and the frame side is already established by this layer's
existing 600-arm walk — `FrameLocal.lean`'s `builtins_run_locals` — for a claim
(`LocalsSame`) that happened to project only `locals`.

**So `LocalsSame` grew two conjuncts** — every frame's `captured`, and `frames.size` — and the
walk was untouched. The whole cost was three lemmas: `setCurrentFrame` (the one arm in the
layer that writes `frames` at all, and it copies the frame to flip a `Bool`), `setLastMatchValue`
(the same `set!` shape), and one extra `rfl` in the `builtin_arms` macro. Six hundred arms
re-elaborated green with no other change, which is the thing worth recording: the walk was
*already* proving this and only the statement was too weak to say so.

**What is now proved.** `Denote/Sem/StepLocal.lean`:

* `Sealed.of_localsSame` / `FramesWF.of_localsSame` — `LocalsSame` is exactly the frame-side
  congruence of each invariant.
* `builtins_run_seal` / `builtins_run_framesWF` — the same at `Builtins.run`, so a caller owes
  **only the heap clauses**.

**What is left, stated as the specification of the second walk.** Those two lemmas' remaining
hypotheses, verbatim:

```
∀ o cl, procClosure? m'.heap (.ref o) = some cl → ∀ p, cl.captured = some p → <p is sealed>
∀ k n md, methodIn m'.heap k n = some md → ∀ p, md.capturedFrame = some p → <p is sealed>
```

i.e. **`Builtins.run` installs no capturing closure and no capturing method**. Both are true —
the layer's only closure allocation is `Symbol#to_proc`, which since L266 captures `none`
(`toProcSealsB` `#guard`s it) — but "true" is not "walked", and this is a second traversal of
the same six hundred arms.

**And it will not ride the first one**, which is worth knowing before starting. Nearly every
arm discharges `LocalsSame` through `LocalsSame.of_eq rfl rfl` — *frames* unchanged — while the
heap is exactly what those arms *do* change, by allocation. So a heap conjunct cannot be added
to `LocalsSame`: `of_eq` has no heap hypothesis to discharge it with, and giving it one changes
all six hundred call sites. The second walk needs its own predicate (allocation-monotone: "every
appended object is not a capturing closure, and not a class with a capturing method") and its own
copy of the twenty machine-threading helper lemmas. That is the honest price, and it is a clink.

### The second walk, **built — `BuiltinsSeal` is proved** (2026-09-10)

`Denote/Sem/BuiltinsCap.lean` (the predicate and the lemmas) plus one module per dispatcher.
All six are proved and axiom-clean — `runRegex` 19 s, `runModules` 48 s, `runCollections` 3 s,
`runStrings` 7 s, `runNumerics` 5 s, `runObjects` 5 s — and `BuiltinsCapRun.lean`'s
**`builtinsSeal : BuiltinsSeal`** joins the heap half to `FrameLocal.lean`'s frame half through
`Sealed.of_capMono`. `builtinsFramesWF` is the bookkeeping twin `Sealed.push` needs beside it.
So the eighteenth stall point is closed: `Sealed` survives `Builtins.run`.

**And the closer set for the `stepFn` walk is now complete** (`Denote/Sem/StepInterp.lean`).
`StepLocal.lean` had the three composites a heap-free machine change needs (`Step.frameOnly`,
`Step.pop`, `Step.setLocal`); `Step.builtins` came with the walk above; and this file adds the
two kinds the *interpreter* makes and a builtin never did —

* **`Step.alloc`**, stated over **`CapAt`** rather than over `Sealed.alloc`'s two `ReachesB`
  premises, precisely so the `cap_free` closers built for the `Builtins` walk discharge it
  unchanged (one pure term per payload iota cannot reduce); and
* **`Step.push_free`/`push_clos`/`push_meth`**, which between them cover **all six**
  `frames.push` sites — the four that default `captured` to `none` (ordinary method frames and
  class bodies) close with no side condition, and the two that set it read a `Closure` or a
  `MethodDef` out of the heap, which is exactly what `Sealed`'s `clos` and `meth` clauses exist
  for. The L266 `Option` and the L267 `meth` arm are what make the first four vacuous and the
  last two lookups.

So every machine change `stepFn` performs has a named closer, and the remaining work in this
layer is the per-arm walk itself — `evalExpr`'s 43 arms, `applyKont`/`unwind`, and the
`Dispatch`/`Send`/`Reflect` helpers — with the eight tactic measurements below as the method.

### …and the walk has to be built **bottom-up**, which cost a run to learn (2026-09-10)

`Denote/Sem/StepWalk.lean` states the target (`StepSound`) and `stepSound_of` decomposes it into
`EvalExprSound`/`ApplyKontSound`/`UnwindSound`. The first attempt at `EvalExprSound` was a single
closer-list tactic over `evalExpr`'s 43 arms, and it **does not terminate** — 20 000 000
heartbeats, 8½ minutes, `timeout at whnf`.

The cause is not the arm count and not the closers. `evalExpr`'s send arms *delegate* — to
`startArgs` (×3), `finishSend`, `enterUserMethod`, `startSuperArgs` (×2), `doSuper`,
`startYield`, `enterClassBody` (×2), `doReturn`, `evalDefined`, `continueArray`,
`undefNames`/`undefAliasMiss`, plus `lookup` (×3) and `defineMethod` (×3) — and with no `Step`
lemma for any of them the tactic has nothing to close those arms with, falls through to
`split at hstep`, and unfolds the whole `Dispatch`/`Send`/`Reflect` layer inside `isDefEq`.

**`RubyCore/Proof/KontFrame.lean` did not make this mistake**, and its order is the correction:
helpers first (`printArm_frame`, `binArg_frame`, `numBin_frame`, `numCmp_frame`,
`withIndex_frame`), then the dispatchers, then `Builtins.run`, then the layers above. So the
companion to this file's existing working rule — *write the layer's target down as a named `Prop`
before proving the layer under it* — is: **prove the callees before the callers, because a
missing helper lemma does not fail, it inlines.** That is the third time measurement order has
cost this layer a run (`FrameLocal.lean`'s false target, `BuiltinsSeal`'s frame-half-first, and
now this), and it is the first time the failure mode was *non-termination* rather than a wrong
theorem.

`Denote/Sem/StepEval.lean` records the five-stage order the walk needs — `Support`, `Dispatch`,
`Send`, `Reflect`, then `evalExpr`, then `applyKont`/`unwind` — with `StepThrough` as the shape
each helper lemma takes and `Step.builtins` as the one entry already discharged (`Builtins.run`
is the bottom of the chain and is done).

**One closer must not be in a list that does not need it**, and this is worth keeping separately
because it is not about ordering: `Machine.setLocal` walks the capture chain *by recursion*, so
unifying a goal's machine against `setLocal ?m ?x ?w` unfolds a recursive function. `evalExpr`
never calls it — `.vasgn` pushes an `.asgnK` and the write happens in `applyKont` — so
`Step.setLocal`/`setLocal'` belong to `ApplyKontSound`'s closer list and nowhere else.

The prediction above was right about the *shape* — its own predicate and its own copy of the
twenty helpers — and wrong about where the cost sat. The lemmas were an afternoon; the **tactic**
was the whole difficulty, and it is worth writing down because it is a reusable technique for any
future walk over this interpreter.

**The predicate.** `CapMono h h'` — every capture edge readable at `h'` was already readable at
`h`, **existentially in the object id**. Not id-keyed, and `Object#dup` is why: `dupObj` pushes a
fresh object carrying the *source's* payload, so `p.dup` on a Proc puts the same edge at a new
id. The seal does not care (`Sealed.clos` at the source discharges it), so the id-keyed version
is a refutation and the existential one is what `Sealed`'s own clauses consume. Measured, not
predicted: the first version would not close for `dupObj`.

`CapAt` is keyed on `methodOf` — the **first** entry of a name, which is what `methodIn` reads —
rather than on membership in `cp.methods`. A membership-shaped `CapAt` would be a claim this file
could establish and `Sealed.meth` could not consume. The sixth stall point's rule (*state the
component over the lookup function*), one layer down.

**The tactic, in eight measurements, each of which cost a full run.** The lemmas were an
afternoon; every one of these was a day. The frame walk closes the
same six hundred arms in **89 s**; the first version of this one had not finished in **thirty-five
minutes**, and `sample` on the live process said why — 60 % of it in
`whnfImp`/`tryHeuristic`/`reduceMatcher?`/`getStuckMVar?`, i.e. unification against stuck
metavariables rather than proof search.

1. **Put the arm's shape in a `rfl`-provable hypothesis; leave the conclusion first-order.** This
   is the whole thing. `LocalsSame.of_eq rfl rfl` is cheap because its conclusion is
   `LocalsSame m ?m'` — unifies with any goal in one step — and everything specific is an
   equation between *projections*. `CapMono.push` concluding `CapMono ?h ⟨?h.objs.push ?obj⟩` is
   the opposite: to *fail* on a non-allocating arm the unifier has to unfold
   `Builtins.allocStr`/`Heap.alloc` against a machine-sized term. `MCap.push_eq`/`set_eq`/
   `push_trans_eq`/`set_trans_eq`/`fold_eq` are the repair, and every one has a first-order
   conclusion. **35 min → 25 s.**
2. **`split at h` first, not last.** The frame walk puts the closers first and `split at h` last.
   Here that costs two 12 s spikes on the *first* goal alone: before any split, `h`'s type is the
   undivided match over `bid`, and every helper closer unifies against a stuck match with
   hundreds of arms. Splitting before closing removes it outright.
3. **No nested `by` in a closer.** `CapMono.push (fun _ hc => by simp at hc)` is tried on every
   leaf of six hundred arms, and a `simp` on a machine-sized goal is a search, not a side
   condition. Every side condition here is a pure term — `fun _ hc => hc` where the payload's
   constructor makes `CapAt` reduce to `False` by iota, `Option.noConfusion` for the layer's one
   Proc allocation (`Symbol#to_proc`, `captured := none` since L266), `capAt_cls_nil` for its one
   class allocation (`Class.new`, `methods := []`) — and where it cannot be a term,
   `refine … ?_` defers it to a **goal**, by which time the object is assigned.
4. **`cap_norm` before the closers** — `RubyCore/Proof/KontFrame.lean`'s `frame_simp` technique.
   Unfolding the sixteen machine-threading helpers *once, in the goal* replaces fifteen expensive
   goal-keyed unification failures with one `simp only`. `apply_ite`/`ite_self` belong in the set
   for `setLastMatchValue`, whose two branches differ in `frames` and agree on `heap`.
5. **A fold lemma applied through `trans` never fires.** `foldPair_cap`'s conclusion is
   `MCap ?p.2 (?l.foldl ?f ?p).2`, so `MCap.trans (foldPair_cap _ ?_ _ _) ?_` asks unification to
   solve `?p.2 ≟ m` — a projection against a metavariable, which it cannot do. The branch fails
   **silently** and leaves the arm open (`Regexp#names` is the arm, and it is what found this).
   Passing a concrete second argument works and reintroduces item 1's cost; `MCap.fold_eq`, which
   reads the fold off the goal by `rfl`, is the version that is both correct and cheap.

**And split the walk one dispatcher per module.** Lean buffers a module's messages until the
module ends — verified, a 5 s `IO.sleep` between two `#print axioms` markers emits both at the
same timestamp under `--json` — so one file holding all six is a black box for as long as it runs,
and a failure in the last discards the first five. Split, `lake` prints a line per dispatcher and
caches each success, and each dispatcher pays only for **its own** expensive closers:
`printFold`/`pGo` are `Object#print`/`p` (`runObjects`) and `setClassPayload_methods` is
`Module#private_constant` (`runModules`), so four of the six use the cheap `cap_arms` and two use
`cap_arms_ctx`. `set_option profiler true` with a threshold is how the 12 s spikes were found;
`sample <pid>` is how their cause was.

6. **A closer's side condition must be a *pure term*, and the fourth violation cost 14 GB.**
   Items 1–3 are all the same lesson, and it kept being relearned in new clothing: a
   `simp only [CapAt] at hc` closer, added because the elaborator will not unfold `CapAt` to
   expose an `Eq` in argument position (`Option.noConfusion hc` fails on
   `hc : CapAt obj p`), took `runStrings` from 7 s to fine but is the prime suspect for
   `runNumerics`. `capAt_proc_none`/`capAt_emptyCore`/`capAt_cls_nil` are the three lemmas that
   replace it — one per payload iota cannot reduce (a Proc's `captured = none`, `Class#allocate`'s
   `emptyCorePayload` *call*, `Class.new`'s empty method table).
7. **Four arms needed hand-written closers, and that is normal.** `FrameLocal.lean` hand-writes
   `newImpl_locals` for the same reason. Here they are in `BuiltinsCapStrings.lean`: `String#[]`
   with a `Regexp` selector *delegates to `runRegex`* (so `runStrings` needs the regex tail, which
   is also why the per-module closer split has to follow delegation and not just file names),
   `Symbol#to_proc`, and `String#freeze` on a `dup` — the last needing `push_copy_then_set`,
   because `MCap.trans` would have to be handed the intermediate machine and
   `?mid.heap.objs ≟ m.heap.objs.push cpy` is the shape problem again. Also: `simp at h` runs
   *before* the leaf closers get the goal, so it has already unfolded `dupObj` — a closer keyed on
   a helper the fallback `simp` dissolves can never fire.
8. **`simp at h` was the whole `runNumerics` problem, and `dsimp only at h` is the whole fix.**
   With `simp` reachable early, `runNumerics` took the elaborator past **14 GB of proof term
   without terminating**; with it demoted below the unfolds and `dsimp only at h` in its place,
   the same file closes in **5 s**. The reason is exact: on an arithmetic arm `simp` tries to
   *evaluate* the `Int`/`Float` literals, while the one thing it was actually needed for is
   beta-reducing a `(fun b => match …) b` arm so `split` can see the match — which `dsimp` does
   definitionally and for free. Two smaller ordering facts came out of the same measurement:
   `Builtins.withIndex` must be unfolded **before** `split at h` (it takes a continuation, so
   `split` otherwise peels the `if`s inside its lambda and strands the arm), and every dispatcher
   needs the **fall-through** closers for the dispatchers below it in the chain — `runNumerics`'
   last open goal was `runStrings bid recv args m = .ok v m'`, which is just `runStrings_cap h`.
   This is the eighth measurement and the fourth instance of item 3: *a `simp` in a 600-arm walk
   is a search, not a step.*

## The remaining 35, re-audited 2026-09-10 — and **seven are false as stated**

Written because "35 remaining" reads as 35 units of work, and the useful fact is that a
identifiable subset is not work at all: those obligations are **false**, and every repair path
for them crosses into `Ratchet/`.

The distinction that matters is not *hard vs. easy*. It is:

| kind | count | what it needs |
|---|---|---|
| **(A) false as stated, repair is in `Ratchet/`, and the rule is *not* unsound** | 7 | a `Judge` premise or a `Ty`/`joinT` change |
| **(B) true, behind the locals + call layer** | 26 | the walk this file specifies — ordinary work |
| **(C) true, behind `PrimSig` row by row** | 1 (`prim`) | ~200 conformance facts, two per row (13th stall point) |
| **(D) true, behind the declaration redesign** | 1 (`classStmt`/`moduleStmt` share it) | `Ctx` recording the cref |

### (A), rule by rule, with the witness for each

* **`defStmt`** — *newly confirmed by construction, not inferred.* `Obl.Judge.defStmt` is
  **premise-free** (`#print` it: it quantifies over every `κ`), its conclusion carries
  `StateOk κ Γ I m'`, and `DefsOk κ.defs m'` demands that every recorded entry's body be the
  *installed* one. `RubyCore.defineMethod` **replaces**. So at `κ.defs = [⟨"foo", [], .int 1⟩]`
  and a conformant machine, running `def foo; "s"; end` falsifies it. Repair: a premise
  (`defGet? κ.defs n = none`, or the threading the sixth stall point describes). **The rule is
  not unsound** — the sixth stall point checked `validate` on the reproducer and it is right —
  so this is not the unsoundness exception, it is a `Judge` signature change.
* **`arrayLit`, `hashLit`** — the seventh stall point's remnant, and it is a *falsity*: a later
  element can mutate an earlier one, so `DenAllAt`'s per-element machines cannot be moved to the
  literal's final machine (`corpus/242-array-lit-element-mutated-unsafe` is the witness). The
  three candidate repairs are recorded there; `Ty.arrayOf` cannot express one machine per
  element, a purity premise is `Ratchet/`, and the `Later`-quantified `.arrayOf` arm does not
  actually transport (it makes the *establishing* side harder, not the consuming side easier).
* **`casgn`, `cpathAsgn`** — false twice over, independently: the seventeenth stall point
  (`ConstScopeOk` is falsified by a class body's first constant, and the component sits on both
  sides of the implication so the fix is a weakening that breaks the three `.const` rungs), and
  §F22 (`constAsgnOk`'s guard list is not the set of class names a `Ty` can carry; `Regexp` is
  outside it, measured). Both repairs are `Ratchet/`: the first wants `Ctx` to record the cref,
  the second wants the guard widened.
* **`if'`, `ifNoElse`** — the eleventh stall point, with an explicit two-environment witness:
  `joinEnv` synthesises a `Ty.sameAs` that neither branch promised, and `EnvOk`'s identity
  conjunct does not fire on a union of aliases. Repair 1 (strengthen `EnvOk` over `unionMems`) is
  `Denote`-only but re-opens `Judge.vasgn`'s §F5 premise, which is `Ratchet/`; repair 2 (strip
  aliases in `joinT`'s union arm) moves the checker's output types and therefore the syntactic
  ratchet.

### What that means for a "climb to 83/83" instruction

**Seven of the 83 obligations cannot be discharged without editing `Ratchet/`**, and none of the
seven is an unsoundness — so the standing exception ("if a `Judge` rule looks genuinely unsound,
fix it") does not reach them. They are false because the *judgment's shape* and the
*denotation's* shape disagree, which is the sixth, seventh, eleventh and seventeenth stall points
saying the same thing from four directions: `Judge` was designed to be checked, not to be
denoted, and four of its rules re-assert an incoming context or a snapshot the semantics has
already invalidated.

This is worth stating as a **precondition** rather than as a stall: the ladder's ceiling under a
no-`Ratchet/` constraint is **76 of 83**, not 83. Reaching 83 requires either the declaration
redesign (`Judge` threading a cref, and premises on `defStmt`/`casgn`) or a decision to move
`joinT`/`constAsgnOk` and re-run the syntactic ratchet. Both are `Ratchet/` work, both are
sized in `context-splitting.md` and the stall points, and neither is blocked on anything in
`Denote/`.
