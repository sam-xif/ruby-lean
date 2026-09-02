import RubyCore.Interp

set_option maxHeartbeats 40000000 in
/-!
# `RubyCore/Proof/NotDone.lean` — `.done` comes from exactly one place

`StepResult.done` is constructed at **one** site in the interpreter (`applyKont`'s empty-
continuation arm), and `applyKont` is called from **one** place (`stepFn`). So no helper can
produce it — and that fact, mechanical as it is, is what lets a run be *inverted*:

    stepFn m = .done v m'  →  m.ctl = .value v ∧ m.kont = [] ∧ m' = m

which is the inversion the run-level decomposition needs. Without it, "the isolated sub-run
stopped here" says nothing about *where* here is, and the pushed run cannot be continued from
the corresponding state.

The chain is the framing chain again, minus `Builtins` (which returns `BRes`, not
`StepResult`) and minus the two-sided matching that made framing expensive: every goal here
has one side.
-/

set_option autoImplicit true
set_option maxRecDepth 400000

namespace RubyCore
namespace Proof

open Builtins
open Interp

set_option maxHeartbeats 40000000 in
/-- Is this step result the run's own end? -/
def isDone : StepResult → Bool
  | .done _ _ => true
  | _ => false

/-- …lifted to the `try*` family's `Option StepResult` (`none` = "not mine, fall through").
A `Bool` on the *goal* side rather than a `∀ sr, … = some sr → …`, because then the walker's
`split` works on the goal and needs no `at h` — which is what the first attempt got wrong. -/
def isDoneO : Option StepResult → Bool
  | some sr => isDone sr
  | none => false

/-- …and to `cpathContainer`, whose *error* side is a step result. -/
def isDoneE {α : Type} : Except StepResult α → Bool
  | .error sr => isDone sr
  | .ok _ => false

/-! ### The reduction lemmas, and why they are lemmas

Passing `isDone` itself to `simp` **unfolds it into its matcher**, which destroys the head
symbol every callee's lemma is keyed on — the goal becomes
`(match callClosure … with | .done _ _ => true | _ => false) = false` and nothing matches it.
So `isDone` is never in a simp set here; these nine `rfl`s are, and the walker runs a bare
`simp`. -/

@[simp] theorem isDone_next (m : Machine) : isDone (.next m) = false := rfl
@[simp] theorem isDone_done (v : Value) (m : Machine) : isDone (.done v m) = true := rfl
@[simp] theorem isDone_uncaught (v : Value) (m : Machine) : isDone (.uncaught v m) = false := rfl
@[simp] theorem isDone_unsupported (r : String) : isDone (.unsupported r) = false := rfl
@[simp] theorem isDone_stuck (r : String) : isDone (.stuck r) = false := rfl
@[simp] theorem isDoneO_none : isDoneO none = false := rfl
@[simp] theorem isDoneO_some (sr : StepResult) : isDoneO (some sr) = isDone sr := rfl
@[simp] theorem isDoneE_ok {α : Type} (a : α) : isDoneE (Except.ok a : Except StepResult α) = false := rfl
@[simp] theorem isDoneE_error {α : Type} (sr : StepResult) :
    isDoneE (Except.error sr : Except StepResult α) = isDone sr := rfl

/-- The bridge for the `try*` family's callers. `split` on `match tryReflect … with | some sr
=> sr | none => …` leaves the goal `isDone sr = false` and the *hypothesis*
`tryReflect … = some sr`; the callee's lemma is about `isDoneO (tryReflect …)`, a term the goal
no longer contains. Taking the hypothesis **first** lets `assumption` find it and fix `o`, and
then `simp` proves the callee's lemma at that `o`. One walker alternative covers every caller
in the file. -/
theorem isDone_of_optNotDone {o : Option StepResult} {sr : StepResult}
    (h : o = some sr) (hnd : isDoneO o = false) : isDone sr = false := by
  rw [h] at hnd; exact hnd

/-- …and the same for `cpathContainer`'s error side. -/
theorem isDone_of_excNotDone {α : Type} {e : Except StepResult α} {sr : StepResult}
    (h : e = .error sr) (hnd : isDoneE e = false) : isDone sr = false := by
  rw [h] at hnd; exact hnd

/-- The walker. One side, so `split` cannot desynchronise anything, and `simp` closes each arm
against the callees' lemmas — all tagged `@[simp]`, which is why the order of this file is the
call graph's. -/
syntax "nd_walk" : tactic
macro_rules
  | `(tactic| nd_walk) =>
    -- **No `rfl` and no `simp_all`.** Both are expensive here for the same reason: the
    -- delegating arms name functions compiled by well-founded recursion, so `rfl` tries to
    -- unfold one and burns the theorem's whole heartbeat budget before `simp` — which closes
    -- these goals in one rewrite against the callee's own lemma — ever gets a turn.
    `(tactic| repeat' first
                | (simp only [isDone_next, isDone_unsupported, isDone_stuck,
                             isDone_uncaught, isDoneO_none, isDoneO_some, isDoneE_ok,
                             isDoneE_error]; done)
                -- `have`-bound (`let_fun`) bodies block `split`; this zeta-reduces them
                | dsimp only
                | (simp (maxSteps := 20000); done)
                -- late, and only for the arms whose goal is `isDone sr = false` with the
                -- callee's `= some sr` in a hypothesis: `simp` on the goal alone cannot use it
                | (simp_all (maxSteps := 20000); done)
                | exact isDone_of_optNotDone (by assumption) (by simp)
                | exact isDone_of_excNotDone (by assumption) (by simp)
                | split)

set_option maxHeartbeats 40000000 in
@[simp] theorem doReturn_notDone : isDone (Interp.doReturn m v) = false := by
  rw [Interp.doReturn.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem callClosure_notDone : isDone (Interp.callClosure m cl args brk selfOv defmodOv) = false := by
  rw [Interp.callClosure.eq_def]
  nd_walk

-- diagnostic
example (m : Machine) (cl : Closure) (args : List Value) (brk : Option FrameId) :
    isDone (Interp.callClosure m cl args brk) = false := by simp

example (m : Machine) (cl : Closure) (args : List Value) (brk : FrameId) (kind : IterKind)
    (acc : List Value) (retVal : Value) (rest : List (List Value)) :
    isDone (Interp.callClosure
      { ctl := m.ctl, kont := Kont.iterK cl brk rest kind acc retVal (args.headD .nil) :: m.kont,
        stack := m.stack, frames := m.frames, heap := m.heap, globals := m.globals,
        out := m.out, currentExc := m.currentExc, preludeMode := m.preludeMode }
      cl acc (some brk)) = false := by simp

set_option maxHeartbeats 40000000 in
@[simp] theorem missNoMethod_notDone : isDone (Interp.missNoMethod m recv site mname args) = false := by
  rw [Interp.missNoMethod.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem visError?_notDone : isDoneO (Interp.visError? m recv site md mname) = false := by
  rw [Interp.visError?.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem cpathContainer_notDone : isDoneE (Interp.cpathContainer m base) = false := by
  rw [Interp.cpathContainer.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem enterClassBody_notDone : isDone (Interp.enterClassBody m name isMod sup? body) = false := by
  rw [Interp.enterClassBody.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem enterScopedClassBody_notDone : isDone (Interp.enterScopedClassBody m container name isMod body) = false := by
  rw [Interp.enterScopedClassBody.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
/-- The largest function in the interpreter, and the same `generalize`-first move its framing
lemma needs (`Proof/KontFrameDispatch.lean`): `classifyFull md.params` is machine-free and
occurs some twenty times. -/
@[simp] theorem enterUserMethod_notDone (m : Machine) (recv : Value) (mname : String)
    (md : MethodDef) (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    isDone (Interp.enterUserMethod m recv mname md args blk kw) = false := by
  rw [Interp.enterUserMethod.eq_def]
  generalize Interp.classifyFull md.params = fp?
  cases fp? with
  | none => simp
  | some fp =>
    simp only [Option.isNone_some, Option.getD_some, Bool.false_eq_true, if_false, reduceIte]
    nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem iterStep_notDone : isDone (Interp.iterStep m cl brk rest kind acc retVal) = false := by
  rw [Interp.iterStep.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem startIter_notDone : isDone (Interp.startIter m recv mname cl elemArgs kind initAcc retVal) = false := by
  rw [Interp.startIter.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem tryIterator_notDone : isDoneO (Interp.tryIterator m recv mname args blk) = false := by
  rw [Interp.tryIterator.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem tryMixin_notDone : isDoneO (Interp.tryMixin m recv mname args) = false := by
  rw [Interp.tryMixin.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectDefineMethod_notDone : isDoneO (Interp.reflectDefineMethod m recv mname args blk) = false := by
  rw [Interp.reflectDefineMethod.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectEval_notDone : isDoneO (Interp.reflectEval m recv mname args blk) = false := by
  rw [Interp.reflectEval.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectCatch_notDone : isDoneO (Interp.reflectCatch m recv mname args blk) = false := by
  rw [Interp.reflectCatch.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectThrow_notDone : isDoneO (Interp.reflectThrow m recv mname args blk) = false := by
  rw [Interp.reflectThrow.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectVisibility_notDone : isDoneO (Interp.reflectVisibility m recv mname args blk) = false := by
  rw [Interp.reflectVisibility.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectSingletonClass_notDone : isDoneO (Interp.reflectSingletonClass m recv mname args blk) = false := by
  rw [Interp.reflectSingletonClass.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectIvarGet_notDone : isDoneO (Interp.reflectIvarGet m recv mname args blk) = false := by
  rw [Interp.reflectIvarGet.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectIvarSet_notDone : isDoneO (Interp.reflectIvarSet m recv mname args blk) = false := by
  rw [Interp.reflectIvarSet.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectIvarNames_notDone : isDoneO (Interp.reflectIvarNames m recv mname args blk) = false := by
  rw [Interp.reflectIvarNames.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectConstGet_notDone : isDoneO (Interp.reflectConstGet m recv mname args blk) = false := by
  rw [Interp.reflectConstGet.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectConstSet_notDone : isDoneO (Interp.reflectConstSet m recv mname args blk) = false := by
  rw [Interp.reflectConstSet.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectRemoveMethod_notDone : isDoneO (Interp.reflectRemoveMethod m recv mname args blk) = false := by
  rw [Interp.reflectRemoveMethod.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectAliasMethod_notDone : isDoneO (Interp.reflectAliasMethod m recv mname args blk) = false := by
  rw [Interp.reflectAliasMethod.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectAttr_notDone : isDoneO (Interp.reflectAttr m recv mname args blk) = false := by
  rw [Interp.reflectAttr.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectMethodDefined_notDone : isDoneO (Interp.reflectMethodDefined m recv mname args blk) = false := by
  rw [Interp.reflectMethodDefined.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem reflectRespondTo_notDone : isDoneO (Interp.reflectRespondTo m recv mname args blk) = false := by
  rw [Interp.reflectRespondTo.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem tryReflect_notDone : isDoneO (Interp.tryReflect m recv mname args blk) = false := by
  rw [Interp.tryReflect.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
set_option maxHeartbeats 40000000 in
set_option maxHeartbeats 40000000 in
/-- The funnel, and the one shape the walker cannot do on its own. `split` on
`match tryIterator … with | some sr => sr | none => …` leaves the goal `isDone sr = false`
with `tryIterator … = some sr` as a *hypothesis*, and the callee's lemma is about
`isDoneO (tryIterator …)` — a term the goal no longer contains. Putting the callee lemmas in
the context first fixes it: `simp_all` rewrites *them* with the hypothesis, turning
`isDoneO (tryIterator …) = false` into `isDone sr = false`, which is the goal. -/
@[simp] theorem dispatchMiss_notDone (m : Machine) (recv : Value) (implicit : SendSite)
    (mname : String) (args : List Value) (blk : Option Value) :
    isDone (Interp.dispatchMiss m recv implicit mname args blk) = false := by
  rw [Interp.dispatchMiss.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
set_option maxHeartbeats 40000000 in
@[simp] theorem invokeDispatch_notDone (m : Machine) (recv : Value) (implicit : SendSite)
    (mname : String) (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    isDone (Interp.invoke.invokeDispatch m recv implicit mname args blk kw) = false := by
  rw [Interp.invoke.invokeDispatch.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem invokeMaybeNew_notDone : isDone (Interp.invoke.invokeMaybeNew m recv o c implicit mname args blk kw) = false := by
  rw [Interp.invoke.invokeMaybeNew.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
/-- Self-recursive on the `send`/`public_send`/`__send__` unwrapping (`termination_by
args.length`), so an induction on `args` with everything else generalised — the same shape as
its framing lemma. -/
@[simp] theorem invoke_notDone (m : Machine) (recv : Value) (implicit : SendSite)
    (mname : String) (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    isDone (Interp.invoke m recv implicit mname args blk kw) = false := by
  induction args generalizing m recv implicit mname blk kw with
  | nil => rw [Interp.invoke.eq_def]; nd_walk
  | cons a rest ih =>
    rw [Interp.invoke.eq_def]
    repeat' first
      | (simp only [isDone_next, isDone_unsupported, isDone_stuck, isDone_uncaught]; done)
      | dsimp only
      | (rw [ih]; done)
      | (simp (maxSteps := 20000); done)
      | (simp_all (maxSteps := 20000); done)
      | exact isDone_of_optNotDone (by assumption) (by simp)
      | exact isDone_of_excNotDone (by assumption) (by simp)
      | split

set_option maxHeartbeats 40000000 in
@[simp] theorem doSuper_notDone : isDone (Interp.doSuper m args blk kw) = false := by
  rw [Interp.doSuper.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem startSuperArgs_notDone : isDone (Interp.startSuperArgs m acc rest blk) = false := by
  rw [Interp.startSuperArgs.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem classNewBlock_notDone : isDone (Interp.classNewBlock m recv args v isClass) = false := by
  rw [Interp.classNewBlock.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem finishSend_notDone : isDone (Interp.finishSend m recv implicit mname args pblk kw) = false := by
  rw [Interp.finishSend.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem startKwargs_notDone : isDone (Interp.startKwargs m recv implicit mname posArgs kwacc entries pblk) = false := by
  rw [Interp.startKwargs.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem startArgs_notDone : isDone (Interp.startArgs m recv implicit mname acc rest pblk) = false := by
  rw [Interp.startArgs.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem doYield_notDone : isDone (Interp.doYield m args) = false := by
  rw [Interp.doYield.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem startYield_notDone : isDone (Interp.startYield m acc rest) = false := by
  rw [Interp.startYield.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem continueArray_notDone : isDone (Interp.continueArray m acc rest) = false := by
  rw [Interp.continueArray.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem forStep_notDone : isDone (Interp.forStep m targets body rest coll) = false := by
  rw [Interp.forStep.eq_def]
  nd_walk

/-- The continuation-taking one, so the hypothesis is pointwise — and as a *conditional* simp
lemma it still fires at the four `*splat` arms, because `simp` discharges the side goal from
the same set. -/
@[simp] theorem withSpread_notDone (m : Machine) (v : Value)
    (k : Machine → List Value → StepResult)
    (hk : ∀ (m₂ : Machine) (vs : List Value), isDone (k m₂ vs) = false) :
    isDone (Interp.withSpread m v k) = false := by
  rw [Interp.withSpread.eq_def]
  cases hsp : Interp.spreadA m v with
  | error e => simp
  | ok p => obtain ⟨vs, m₂⟩ := p; exact hk m₂ vs

set_option maxHeartbeats 40000000 in
@[simp] theorem undefAliasMiss_notDone : isDone (Interp.undefAliasMiss m name) = false := by
  rw [Interp.undefAliasMiss.eq_def]
  nd_walk

/-- Recursive, so an induction on the name list. -/
@[simp] theorem undefNames_notDone (m : Machine) (defmod : ObjId) :
    ∀ (l : List String), isDone (Interp.undefNames m defmod l) = false := by
  intro l
  induction l generalizing m with
  | nil => rw [Interp.undefNames.eq_def]; simp
  | cons a rest ih =>
    rw [Interp.undefNames.eq_def]
    repeat' first
      | (simp only [isDone_next, isDone_unsupported, isDone_stuck, isDone_uncaught]; done)
      | dsimp only
      | (rw [ih]; done)
      | (simp (maxSteps := 20000); done)
      | split

set_option maxHeartbeats 40000000 in
@[simp] theorem unwind_notDone : isDone (Interp.unwind m j) = false := by
  rw [Interp.unwind.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem evalDefined_notDone : isDone (Interp.evalDefined m e) = false := by
  rw [Interp.evalDefined.eq_def]
  nd_walk

set_option maxHeartbeats 40000000 in
@[simp] theorem evalExpr_notDone : isDone (Interp.evalExpr m e) = false := by
  rw [Interp.evalExpr.eq_def]
  nd_walk

/-- `applyKont` at a *non-empty* continuation: every arm either steps, gates, or unwinds —
none of them is the run's own end. -/
@[simp] theorem applyKont_notDone (m : Machine) (v : Value) (hne : m.kont ≠ []) :
    isDone (Interp.applyKont m v) = false := by
  rw [Interp.applyKont.eq_def]
  cases hk : m.kont with
  | nil => exact absurd hk hne
  | cons k rest => nd_walk

/-- **The inversion**, and the only thing this file exists for: `.done` is constructed at one
site (`applyKont`'s empty-continuation arm) and `applyKont` is called from one place
(`stepFn`), so a step that ends the run tells you exactly what state it ended in. -/
theorem done_inv (m : Machine) (v : Value) (m' : Machine) (h : Interp.stepFn m = .done v m') :
    m.ctl = .value v ∧ m.kont = [] ∧ m' = m := by
  cases hc : m.ctl with
  | eval e =>
    simp only [Interp.stepFn, hc] at h
    have hnd := evalExpr_notDone (m := m) (e := e)
    rw [h] at hnd
    exact absurd hnd (by simp)
  | jump j =>
    simp only [Interp.stepFn, hc] at h
    have hnd := unwind_notDone (m := m) (j := j)
    rw [h] at hnd
    exact absurd hnd (by simp)
  | value w =>
    cases hk : m.kont with
    | nil =>
      simp only [Interp.stepFn, hc, Interp.applyKont, hk] at h
      cases h
      -- `cases hk : m.kont` has already rewritten the goal's `m.kont` to `[]`
      exact ⟨rfl, rfl, rfl⟩
    | cons k rest =>
      simp only [Interp.stepFn, hc] at h
      have hnd := applyKont_notDone m w (by rw [hk]; simp)
      rw [h] at hnd
      exact absurd hnd (by simp)

#print axioms evalExpr_notDone
#print axioms unwind_notDone
#print axioms done_inv

end Proof
end RubyCore
