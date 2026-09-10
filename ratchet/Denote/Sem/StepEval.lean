import Denote.Sem.StepWalk

/-!
# `Denote/Sem/StepEval.lean` — the **specification** of `EvalExprSound`'s dependency chain

`Denote/Sem/StepWalk.lean` states the layer's target and decomposes it into three arms. This
file is about the first of them, `EvalExprSound`, and it deliberately contains **no proof** —
because the first attempt at one measured something worth writing down.

## The measurement: `evalExpr` cannot be walked before its helpers

A single closer-list tactic over `evalExpr`'s 43 arms **does not terminate** — 20 000 000
heartbeats, 8½ minutes, `timeout at whnf`. The reason is not the arm count and not the closer
list: it is that `evalExpr`'s send arms *delegate*, to `startArgs` (×3), `finishSend`,
`enterUserMethod`, `startSuperArgs` (×2), `doSuper`, `startYield`, `enterClassBody` (×2),
`doReturn`, `evalDefined`, `continueArray`, `undefNames`/`undefAliasMiss` (×3), plus `lookup`
(×3) and `defineMethod` (×3). With no `Step` lemma for any of them the tactic has nothing to
close those arms with, falls through to `split at hstep`, and starts unfolding the entire
`Dispatch`/`Send`/`Reflect` layer — thousands of lines — inside `isDefEq`.

**`RubyCore/Proof/KontFrame.lean` did not make this mistake**, and its shape is the correction:
it proves `printArm_frame`, `binArg_frame`, `numBin_frame`, `numCmp_frame`, `withIndex_frame`
*first*, then the dispatchers, then `Builtins.run`, then the layers above. Bottom-up, one lemma
per helper, so that each caller closes by `exact <helper>_frame …`. The same order is what this
walk needs, and the same order is what `BuiltinsCap*.lean` followed by accident of the chain
(`Builtins` is the bottom).

**This is the third time this layer has paid for measurement order** — `FrameLocal.lean`'s 532
lines proved for a target that was false, `BuiltinsSeal`'s frame half proved before anyone
checked whether the *seal* travelled, and now `evalExpr` attempted before its helpers. The
working rule already in `notes.md` is "write the layer's target down as a named `Prop` before
proving the layer under it"; the companion rule this adds is **"and prove the callees before the
callers, because a missing helper lemma does not fail — it inlines"**.

## The order the walk has to be built in

Bottom-up, each entry a `Step` lemma of the same shape (`StepInv b m → f … = .next m' →
Step b m m'`, or the `BRes`/`Option` variant where the helper returns one):

1. **`Interp/Support.lean`** — `matchGlobal`, `reifyBlock`, `coerceToProc`, `callClosure`
   (the first frame-pusher: `Step.push_clos`), `destructureBind`, `doReturn`, `finishRegion`,
   `enterHandler`, `appendKwHash`, `spread`/`spreadA`. `Step.raiseErr`/`withCtl`/`withKont` and
   the allocators are already here (`StepInterp.lean`).
2. **`Interp/Dispatch.lean`** — `lookup`, `invoke`, `invokeDispatch`, `dispatchMiss`,
   `enterUserMethod` (`Step.push_meth`), `enterClassBody`/`enterScopedClassBody`
   (`Step.push_free`), `defineAttr`, `eigenclassOf`, `missNoMethod`.
3. **`Interp/Send.lean`** — `startArgs`, `continueArgs`, `finishSend`, `startSuperArgs`,
   `doSuper`, `startYield`, `continueArray`.
4. **`Interp/Reflect.lean`** — `evalDefined`, `defineMethod`, `undefNames`, `undefAliasMiss`,
   and the `*_eval` family.
5. **`evalExpr`** — 43 arms, each then one `exact`.
6. **`applyKont`/`unwind`** (`ApplyKontSound`/`UnwindSound`), which additionally need
   `Step.setLocal` for the `.asgnK` arm and `Step.pop` for the frame pops.

`Builtins.run` — the widest layer and the one under all of these — is **done**
(`Step.builtins`, `BuiltinsCapRun.lean`).

## One closer that must not be in the list, measured

`Step.setLocal`/`Step.setLocal'` were in the first attempt's closer list and are **poison for
any walk that does not need them**: `Machine.setLocal` walks the capture chain by recursion, so
unifying a goal's machine against `setLocal ?m ?x ?w` unfolds a recursive function. `evalExpr`
never calls it — `.vasgn` pushes an `.asgnK` and the write happens in `applyKont` — so the
closers belong to `ApplyKontSound`'s list and nowhere else.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **The shape every helper lemma in the chain above takes.** Written as a definition so the
five stages can be stated and checked off individually rather than described in prose. -/
def StepThrough (f : Machine → StepResult) : Prop :=
  ∀ (b : FrameId) (m m' : Machine), StepInv b m → f m = .next m' → Step b m m'

/-- `Step.builtins` in this shape, as the one entry of the chain that is already discharged —
and as a check that `StepThrough` is the right shape to state the rest in. -/
theorem stepThrough_builtins (bid : String) (recv : Value) (args : List Value) :
    ∀ (b : FrameId) (m m' : Machine) (v : Value), StepInv b m →
      Builtins.run bid recv args m = .ok v m' → Step b m m' :=
  fun _ _ _ _ h hrun => Step.builtins h hrun

#print axioms stepThrough_builtins

end Ratchet.Denote
