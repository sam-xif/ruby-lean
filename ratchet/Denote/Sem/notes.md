# `Denote/Sem/notes.md` — the semantic ratchet: how a rung gets climbed

`Denote/notes.md` records why the *denotation* is shaped as it is. This file is about the
second ladder built on top of it: **one rung, one `Judge` rule discharged over that
denotation, proved from `stepFn`.** It is a working procedure, not a design essay — read it
before attempting a rung.

## The pieces, and which of them you never edit

| File | What it is | Hand-edited? |
|---|---|---|
| `Trans.lean` | `toRuby : Ratchet.Expr → RubyCore.Expr` | only when a syntax constructor changes |
| `State.lean` | `Evals`, `StateOk` and its eleven components | yes — a rung that will not close often means a component is wrong |
| `Judge.lean` | the eight `SemJudge*` definitions | yes, same reason |
| `Obligations.lean` | the 83 `Obl.*` — **derived** from the inductive | **no** |
| `../Ladder.lean` | the count, and the `isDefEq` gate | no — except its one `import Denote.Rules` |
| `../Rules.lean` | the list of rule files, so the ladder can see them | yes, one line per new file |
| `../Adequacy.lean` | `AdequacyTarget`, `AdequacyHyps` (derived) | no |
| `../Ext.lean` | `Ext` (allocation) and the probe lemmas across it | yes — a new allocation shape may need a clause |
| `../Grow.lean` | `denM_ext`: a type's meaning survives an allocation | no — it follows `Den.lean` |

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

## `Judge.vasgn` is unsound, and the obligation is what says so

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

Per the working procedure above, the rule was **not worked around**: `Ratchet/` is unmodified
and the rung stays undischarged.

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

**The bad news is the size.** The lemma has to be proved over the whole of `stepFn`.
Measured on `evalExpr` alone: `cases e <;> unfold <;> simp only [withCtl, withKont] <;> cases
h <;> rfl` closes **12 of its 43 arms**; the other 31 need a `split` per inner match, and five
of them (`send`, `yield'`, `super'`, `class'`, `defined`) delegate into
`Interp/Dispatch.lean`, `Interp/Send.lean` and `Interp/Reflect.lean` — ~1700 further lines,
each needing the same commutation. And past those sit the **builtins**: `grep` finds no
`kont :=` under `Builtins/`, so they are kont-transparent, but "this builtin returns a machine
whose `kont` is its argument's" is a frame property that has to be *proved*, over ~24k lines.

Three things follow, and they are the reason this is written down rather than attempted:

* It is **not a `Denote/` lemma**. It is a structural fact about `RubyCore`'s abstract
  machine, and it belongs next to `stepFn` — in `RubyCore/Proof/`, where the metatheory
  already reasons about the continuation stack (by a *typed-stack invariant*, `KontOk`, rather
  than by decomposition — which is the technique that avoids needing this lemma at all, and is
  worth weighing before writing it).
* It blocks **every compound rung**, not just `vasgn`: `if'`, `arrayLit`, `hashLit`, all four
  `JudgeSeq` rules, every call rule. The ladder's next number is gated on it.
* The alternative — redefining `Evals` to quantify over continuations — is a **weakening of
  every obligation**, and must not be taken. `Evals` under an arbitrary `K` is strictly
  stronger as a predicate, and `Evals` sits on the *left* of `SemJudge`'s implication, so
  strengthening it weakens all 83 statements at once, silently, including the ten already
  climbed. The two forms are equivalent exactly when the decomposition lemma holds, which is
  the honest way to get there.

## What is not on this ladder

**Stuck-freedom.** `SemJudge` is partial correctness about the *value*: a run that returns
lands in the type's denotation. It says nothing about whether a run reaches a type-stuck
outcome — the `NoMethodError`/`ArgumentError`/`TypeError` family
`../../type-safety-by-reachability.md` is about, and the property `Ratchet/`'s whole soundness
story ultimately wants. `StuckFree` (`State.lean`) and `StuckFreeTarget` (`../Adequacy.lean`)
state it; nothing counts it. Folding it in would make every rung carry two proofs of different
shapes under one number, and the ladder's number is supposed to mean one thing.
