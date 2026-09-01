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

## The fourth stall point — observed, not predicted: **allocation**

The three above were written before the first attempt. The first rung actually to stall was
none of them. `Judge.strLit` — the third literal, and by the count above a two-`stepFn`
rung like the others — does not close, because `evalExpr` on a `.str` calls
`Builtins.allocStr`: its post-machine's heap is its pre-machine's heap with one object
**pushed**. That is the first rung whose `m'` differs from `m` anywhere but `ctl`, and it
needs two things nothing currently supplies.

1. **`StateOk` says nothing about the boot classes.** The rule concludes `.cls "String"`,
   whose denotation is `isAName m'.heap v "String"` — which resolves the *name* through the
   heap's constant table. A machine conformant with `(κ, Γ, I)` is not required to have a
   class named `String` at all, so the conclusion is not derivable from the hypothesis. This
   is stall point (1) exactly as described, and the missing component is a real one: the
   heap's core classes are what they are. Every rule concluding a builtin class type
   (`strLit`, `arrayLit`, `hashLit`, most of `prim`) will want it.

2. **`denM` does not survive a heap extension**, and cannot be made to cheaply. Re-proving
   `EnvOk Γ m'` means transporting `denM τ m (m.getLocal x)` across the push for an arbitrary
   `τ` — including an arrow, whose denotation quantifies over *runs* (`Returns m f args v m'`).
   A run from the extended heap allocates at shifted object ids, so it is not the run from the
   unextended one; relating the two is an allocation-equivariance simulation over the whole
   interpreter, not a lemma. `AsmsOk` has the same shape and the same problem.

The tempting fix for (2) is the one `Denote/Arrow.lean` already sketches for a different
reason: quantify the arrow arm over machines **reachable** from `m` (`ArrowStable`), making
it monotone along execution by `Reaches.trans`. Note before trying it that it *conflicts*
with the lemma the leaf rungs already rest on: `Denote/Rules/Core.lean`'s `denM_ctl` says the
denotation cannot see `ctl`/`kont`, and machines reachable from `m` are not the machines
reachable from `m` with its control word rewritten. Any reachability-indexed arrow has to be
seeded by something coarser than `Reaches m` — "reachable from `m` under some control word"
is the obvious candidate, and it is a `Denote/Den.lean` change with `DenB`, `Arrow.lean` and
the `Examples.lean` guards downstream of it. Not attempted here; recorded so the next attempt
starts from the constraint rather than discovering it.

## What is not on this ladder

**Stuck-freedom.** `SemJudge` is partial correctness about the *value*: a run that returns
lands in the type's denotation. It says nothing about whether a run reaches a type-stuck
outcome — the `NoMethodError`/`ArgumentError`/`TypeError` family
`../../type-safety-by-reachability.md` is about, and the property `Ratchet/`'s whole soundness
story ultimately wants. `StuckFree` (`State.lean`) and `StuckFreeTarget` (`../Adequacy.lean`)
state it; nothing counts it. Folding it in would make every rung carry two proofs of different
shapes under one number, and the ladder's number is supposed to mean one thing.
