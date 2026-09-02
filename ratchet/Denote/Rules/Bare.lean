import Denote.Rules.Core
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Bare.lean` — the rung whose content is that the run **does not return**

`Judge.bareName` is the first rule on this ladder that is true for a reason no earlier rung
had: not "the value is in the type" but **there is no value**. A bare `x` at top level raises
`NameError`, which is outside the `NoMethodError`/`ArgumentError`/`TypeError` family this
package defines type-safety over (`Ratchet/Judge.lean`), so the rule types it `.any` and
threads `Γ` and the ivar spine out unchanged. Every one of those three claims is vacuous
*provided the call really raises*, and that is the whole obligation: `SemJudge`'s hypothesis
`Evals m (.vcall "x") v m'` has to be **unsatisfiable**.

So this rung is a forward walk through dispatch rather than an inversion of one, and it is the
first rung to touch `Interp/Send.lean` and `Interp/Reflect.lean` at all:

```
evalExpr (.vcall "x")  →  startArgs (no args)  →  finishSend (no block)  →  invoke
  →  invoke.invokeDispatch          -- "x" is not `send`/`new`/a Proc-call verb
  →  dispatchMiss                   -- `lookup` found nothing
  →  missNoMethod                   -- no *user* `method_missing`
  →  .next (raiseErr … nameErrorId) -- and `unwind` at `kont = []` is `.uncaught`
```

**Three of those five arrows are the two `StateOk` components clink 52 added** —
`BareNameFree` for the `lookup` miss, `MissFree` for the `method_missing` one
(`Denote/Sem/State.lean`, and `found-issues.md` §F4 for what the second one's absence cost).
The ninth stall point predicted exactly this: a rule with a **negative** premise needs an
upper bound on the machine, and `NameFreeOk` (clink 51) was the first half of one.

**What the walk does *not* need**, recorded because it is what makes the rung possible at all
before the fifth stall point is resolved: `.vcall` has **no argument expressions**, so no
sub-run is ever evaluated under a pushed continuation and `KontFrame`
(`Denote/Sem/Frame.lean`) is not on the path. `startArgs` at `rest = []` goes straight to
`finishSend`, which is why this rule and `Judge.lambdaLit` were the two the fifth stall point
never blocked.

**Where the three gates go.** `dispatchMiss` consults `crubySingletonShadow`, `crubyShadow`
and `mixinShadow` before it raises, and each of them can answer `.unsupported` — the fragment
gate. That costs the proof nothing and it is worth seeing why: `.unsupported` is not a
`.value` either, so those branches close by the same argument as the `NameError` one. The
`Doomed` predicate below is what lets all four outcomes be discharged once.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Ratchet.Denote

open RubyCore

/-! ## A step result no run can turn into a value -/

/-- **`Doomed r`**: no run continuing from `r` produces a value. Two of the five constructors
are `True` outright (`unsupported`/`stuck` end the run and are not `.value`), `uncaught` the
same, `done` is `False` because a `done` *is* the value, and `next` defers to the machine.

Stated as a `match` on the result rather than as four separate lemmas because the caller
always has a `StepResult` in hand from a `split`, and this way the case analysis happens once. -/
def Doomed : StepResult → Prop
  | .next m => ∀ fuel v m', Interp.run fuel m ≠ .value v m'
  | .done _ _ => False
  | _ => True

/-- **The inversion this rung uses in place of `evals_pure`.** If the first step of the run
lands on a doomed result, the run never returns — so an obligation whose hypothesis is a
returning run has nothing to prove. -/
theorem evals_doomed {m : Machine} {e : Ratchet.Expr} {v : Value} {m' : Machine}
    (hd : Doomed (Interp.stepFn (evalFrom m e))) : ¬ Evals m e v m' := by
  rintro ⟨fuel, hrun⟩
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | fuel + 1 =>
    rw [run_succ] at hrun
    revert hd hrun
    cases h : Interp.stepFn (evalFrom m e) with
    | next m₁ => intro hd hrun; exact hd fuel v m' hrun
    | done w m₁ => intro hd _; exact hd.elim
    | uncaught e₁ m₁ => intro _ hrun; exact absurd hrun (by simp)
    | unsupported r => intro _ hrun; exact absurd hrun (by simp)
    | stuck s => intro _ hrun; exact absurd hrun (by simp)

/-- **A raise with nothing to catch it is doomed.** `raiseErr` allocates the exception and
sets `ctl := .jump (.raiseJ …)`, leaving `kont` where it was; `unwind` at `kont = []` answers
`.uncaught`, which is not a `.value` at any fuel. The `kont = []` hypothesis is the one
`evalFrom` supplies by construction. -/
theorem Doomed_raiseErr {m : Machine} (hk : m.kont = []) (cls : ObjId) (msg : String) :
    Doomed (.next (Interp.raiseErr m cls msg)) := by
  intro fuel v m'
  cases fuel with
  | zero => rw [run_zero]; simp
  | succ f =>
    have hstep : Interp.stepFn (Interp.raiseErr m cls msg) =
        .uncaught (Builtins.allocExc m cls msg).1 (Interp.raiseErr m cls msg) := by
      simp only [Interp.stepFn, Interp.raiseErr, Interp.unwind, Builtins.allocExc, hk]
    rw [run_succ, hstep]
    simp

/-! ## The walk, one interpreter function at a time

Four lemmas, each one arrow of the diagram in the module docstring. They are about `stepFn`
rather than about the rule, so by `Denote/Sem/notes.md`'s division they would belong in
`Rules/Core.lean` — they are here instead because every one of them is *specialised to the
name* `"x"`: the string literal is what decides `invoke`'s `send`-family test, its
Proc-call-verb test and `tryReflect`'s reflective-name match, so none of them generalises to
an arbitrary `mname` without hypotheses that only `BareNameError`'s one row supplies. -/

/-- **`invoke` at a name that resolves nowhere is the miss path.** The first step is the one
worth naming: `invoke`'s five pre-dispatch interceptions (`send`-family re-dispatch, a Proc
receiver's `call`/`()`/`[]`/`yield`, a `Hash` default proc, `Math`/`Regexp` singletons, and
`Class#new` with a user `initialize`) are each keyed on the *name*, so at `"x"` every one of
them falls through to `invokeDispatch` — including the receiver cases (`.proc`, `.hsh`,
`.cls`), which is why nothing here needs a hypothesis about `self`'s payload. Then
`invokeDispatch` at `lookup = none` is `dispatchMiss` with the keyword bundle appended, and
at `kw = []` `appendKwHash` is the identity. -/
theorem invoke_vcall_miss (m : Machine) (recv : Value)
    (h : lookup m.heap recv "x" = none) :
    Interp.invoke m recv .vcall "x" [] none [] = Interp.dispatchMiss m recv .vcall "x" [] none := by
  have step1 : Interp.invoke m recv .vcall "x" [] none [] =
      Interp.invoke.invokeDispatch m recv .vcall "x" [] none [] := by
    unfold Interp.invoke; repeat' split
    all_goals first | rfl | simp_all
  rw [step1]
  unfold Interp.invoke.invokeDispatch
  simp only [h]
  rfl

/-- **`dispatchMiss` at a name with no *user* `method_missing` raises `NameError`** — or gates.
The disjunction is the honest statement: `crubySingletonShadow`, `crubyShadow` and
`mixinShadow` each answer `.unsupported` when CRuby would have a method the model does not,
and that is a fragment gate rather than an outcome this rule is wrong about.

`hmm` is the `MissFree` component, and it is load-bearing: without it exactly one goal is left
open, `enterUserMethod … "method_missing"`, which is `found-issues.md` §F4. -/
theorem dispatchMiss_vcall (m : Machine) (recv : Value)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing" = some (o, md) →
        md.builtin.isSome = true) :
    (∃ r, Interp.dispatchMiss m recv .vcall "x" [] none = StepResult.unsupported r) ∨
    Interp.dispatchMiss m recv .vcall "x" [] none =
      .next (Interp.raiseErr m Boot.nameErrorId
        s!"undefined local variable or method 'x' for {Interp.receiverDesc m.heap recv}") := by
  unfold Interp.dispatchMiss
  simp only [Interp.tryIterator, Interp.tryMixin, Interp.tryReflect]
  repeat' split
  all_goals first
    | (right; rfl)
    | (left; exact ⟨_, rfl⟩)
    | simp_all

/-- One `stepFn` step from `evalFrom`: `evalExpr`'s `.vcall` arm is `startArgs` with an empty
argument list and no block, and both of those collapse definitionally. -/
theorem stepFn_vcall (m : Machine) (n : String) :
    Interp.stepFn (evalFrom m (.vcall n)) =
      Interp.invoke (evalFrom m (.vcall n)) m.currentFrame.self .vcall n [] none [] := rfl

/-- **The rung's content: the run does not return.** -/
theorem vcall_x_doomed {m : Machine}
    (hlook : lookup m.heap m.currentFrame.self "x" = none)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) "method_missing"
        = some (o, md) → md.builtin.isSome = true)
    {v : Value} {m' : Machine} : ¬ Evals m (.vcall "x") v m' := by
  refine evals_doomed ?_
  rw [stepFn_vcall, invoke_vcall_miss _ _ (by exact hlook)]
  rcases dispatchMiss_vcall (evalFrom m (.vcall "x")) m.currentFrame.self
      (by exact hmm) with ⟨r, hr⟩ | hr
  · rw [hr]; trivial
  · rw [hr]; exact Doomed_raiseErr rfl _ _

/-! ## The rung -/

theorem Sem.Judge.bareName : Obl.Judge.bareName := by
  intro κ Γ I n hn hdef hself hmm
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' hev
  cases hn
  exact absurd hev (vcall_x_doomed (hm.bareFree "x" .x hdef hself)
    (hm.missFree hmm hself))

#print axioms Sem.Judge.bareName

end Ratchet.Denote
