import Denote.Sem.StepInterp

/-!
# `Denote/Sem/StepWalk.lean` — the locals layer's target, stated

**Written before the walk under it, which is the working rule this layer has now paid for
three times** (`notes.md`: `KontFrame`'s `not_KontFrame`, `FrameLocal.lean`'s 532 lines proved
for a target that turned out false, and `BuiltinsSeal`'s frame half proved before anyone checked
whether the *seal* travelled). A comment saying "this ought to be true" cannot be attacked; a
named `Prop` can.

`StepSound` is the whole of it: **the interpreter preserves the locals layer, one step**. It is
what `Denote/Sem/StepLocal.lean`'s prose calls the per-step claim, and the correction recorded
there is already built into it — the conclusion is `Step`, which carries `StepInv` at `m'`
(seal, bookkeeping *and* `b < m'.frames.size`) rather than a bare `¬ ReachesFrame`, because a
stack pop can make `b` reachable again.

`stepFn` is a three-way match on `ctl`, so the target decomposes into exactly three, and
`stepSound_of` is that decomposition — cheap, and it means the remaining work is three named
`Prop`s rather than one unbounded one. Sized honestly:

| target | what is under it |
|---|---|
| `EvalExprSound` | `evalExpr`'s 43 arms. Most change only `ctl`/`kont` (`Step.frameOnly`); the literals allocate (`Step.alloc`); `.lvasgn` is `Step.setLocal`; the sends and `.def'`-family delegate into `Dispatch`/`Send`/`Reflect` |
| `ApplyKontSound` | `applyKont`'s continuation arms, including the frame *pops* (`Step.pop`) and `.casgnK`'s class-payload write |
| `UnwindSound` | `unwind`'s jump arms — the `catch` scan, `doReturn`, and the handler entry |

Every machine change any of them performs already has a closer: `Step.frameOnly`/`pop`/
`setLocal` (`StepLocal.lean`), `Step.builtins` (`BuiltinsCapRun.lean`), and
`Step.alloc`/`push_free`/`push_clos`/`push_meth` (`StepInterp.lean`, covering all six
`frames.push` sites). So what is left is the walk, not the vocabulary.

**Nothing in this file assumes any of the three.** `stepSound_of` takes them as hypotheses, so
the decomposition is usable — and checkable — before a single arm is closed.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **The layer's target.** One `stepFn` step leaves `b`'s locals alone and hands the invariant
back. -/
def StepSound : Prop :=
  ∀ (b : FrameId) (m m' : Machine), StepInv b m → Interp.stepFn m = .next m' → Step b m m'

/-- The `ctl = .eval e` arm. -/
def EvalExprSound : Prop :=
  ∀ (b : FrameId) (m m' : Machine) (e : RubyCore.Expr), StepInv b m →
    Interp.evalExpr m e = .next m' → Step b m m'

/-- The `ctl = .value v` arm. -/
def ApplyKontSound : Prop :=
  ∀ (b : FrameId) (m m' : Machine) (v : Value), StepInv b m →
    Interp.applyKont m v = .next m' → Step b m m'

/-- The `ctl = .jump j` arm. -/
def UnwindSound : Prop :=
  ∀ (b : FrameId) (m m' : Machine) (j : Jump), StepInv b m →
    Interp.unwind m j = .next m' → Step b m m'

/-- **The decomposition**, and it is the whole content of `stepFn`: a three-way match on `ctl`
with no work of its own. -/
theorem stepSound_of (he : EvalExprSound) (ha : ApplyKontSound) (hu : UnwindSound) :
    StepSound := by
  intro b m m' h hstep
  rw [Interp.stepFn] at hstep
  cases hc : m.ctl with
  | eval e => rw [hc] at hstep; exact he b m m' e h hstep
  | value v => rw [hc] at hstep; exact ha b m m' v h hstep
  | jump j => rw [hc] at hstep; exact hu b m m' j h hstep

#print axioms stepSound_of

end Ratchet.Denote
