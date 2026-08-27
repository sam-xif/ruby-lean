/-
  RubyCore.HJudge.Lang — the RubyCore machine as an iris-lean `Language`.

  **Ported from `mdd/ruby-sorbet`'s `mdd/sorbet-lean/SorbetLean/Lang.lean`**
  (spike S1, verdict GO), brought in-tree for the H-layer (judgment-layer.md
  J36) with the namespace renamed and nothing else. The original's provenance
  notes are preserved below.

  Instantiation (template: cerberus-lean `RelSem/IrisLang.lean`, golean
  `proofs/GoLeanProofs/Lang.lean`):

    Expr  := RExpr  (a control configuration `MCfg` — the `Machine` minus its
                     heap — or a terminal `ROutcome`)
    State := Heap   (the mutable store; per-object ownership lands here when
                     the state interpretation upgrades from ownP to gen_heap)
    Obs   := Empty  (v0: `Machine.out` stays control-side; stdout can become
                     an observation later without reshaping the instance)
    Val   := ROutcome

  Design decisions, recorded:
  * `Machine` is split by a zero-cost wrapper (`MCfg.load` / `Machine.cfg`,
    round-trip `rfl` by structure eta) — the machine and `stepFn` are consumed
    verbatim, never modified.
  * An uncaught exception is a VALUE, not stuckness (the cerberus
    `killed`-as-value choice; our `StepResult` already reifies outcomes).
    `ROutcome` carries the final heap so type-stuckness (`isTypeError h e`,
    which reads the heap through `isA`) is classifiable on the outcome —
    statement parity with `RubyCore.Proof.TypeSafety.typeStuck`.
  * `.unsupported`/`.stuck` step results have NO step: they are genuinely
    stuck configurations. A NotStuck WP therefore also claims the execution
    stays inside the modelled fragment — honest, and exactly what the
    fragment gate is for.

  House rules (adopted from the siblings): no sorry, no new axioms.
-/
import Iris.ProgramLogic.Language
import Iris.Std.FromMathlib
import RubyCore.Interp

set_option autoImplicit false

namespace RubyCore.HJudge

open RubyCore
open Iris.ProgramLogic
open FromMathlib

/-- The control configuration: `Machine` minus its heap. Locals (frames) are
    control-side — the env-in-config CEK reshape golean records in
    `docs/2026-07-19_env-in-config-cek.md`. -/
structure MCfg where
  ctl : Ctl
  kont : List Kont := []
  stack : List FrameId
  frames : Array Frame
  globals : List (String × Value) := []
  out : String := ""
  currentExc : Option Value := none
  preludeMode : Bool := false
deriving Inhabited

/-- Reassemble a `Machine` from a control configuration and a heap. -/
def MCfg.load (c : MCfg) (h : Heap) : Machine :=
  { ctl := c.ctl, kont := c.kont, stack := c.stack, frames := c.frames,
    heap := h, globals := c.globals, out := c.out,
    currentExc := c.currentExc, preludeMode := c.preludeMode }

/-- Project the control configuration out of a `Machine`. -/
def _root_.RubyCore.Machine.cfg (m : Machine) : MCfg :=
  { ctl := m.ctl, kont := m.kont, stack := m.stack, frames := m.frames,
    globals := m.globals, out := m.out,
    currentExc := m.currentExc, preludeMode := m.preludeMode }

/-- The split is lossless (structure eta makes it definitional). -/
@[simp] theorem load_cfg (m : Machine) : m.cfg.load m.heap = m := rfl

@[simp] theorem cfg_load (c : MCfg) (h : Heap) : (c.load h).cfg = c := rfl

@[simp] theorem heap_load (c : MCfg) (h : Heap) : (c.load h).heap = h := rfl

/-- Terminal outcomes — the language's values. Both carry the final heap:
    classification of an uncaught exception as a type error reads the heap
    (`isA` walks the class chain), and the value case keeps the symmetry. -/
inductive ROutcome where
  | val (v : Value) (h : Heap)
  | exc (e : Value) (h : Heap)
deriving Inhabited

/-- Expressions: a running control configuration or a terminal outcome. -/
inductive RExpr where
  | running (c : MCfg)
  | done (o : ROutcome)
deriving Inhabited

/-- The primitive step: ONE `stepFn` application, no observations, no forks.
    `.unsupported`/`.stuck` results deliberately have no constructor. -/
inductive RStep : RExpr × Heap → List Empty → RExpr × Heap × List RExpr → Prop where
  | next {c : MCfg} {h : Heap} {m' : Machine} :
      Interp.stepFn (c.load h) = .next m' →
      RStep (.running c, h) [] (.running m'.cfg, m'.heap, [])
  | val {c : MCfg} {h : Heap} {v : Value} {m' : Machine} :
      Interp.stepFn (c.load h) = .done v m' →
      RStep (.running c, h) [] (.done (.val v m'.heap), m'.heap, [])
  | exc {c : MCfg} {h : Heap} {e : Value} {m' : Machine} :
      Interp.stepFn (c.load h) = .uncaught e m' →
      RStep (.running c, h) [] (.done (.exc e m'.heap), m'.heap, [])

/-- THE language instance (all fields at once — the cerberus no-diamond
    discipline). -/
instance instLanguageRuby : Language RExpr Heap Empty ROutcome where
  toVal | .done o => some o | .running _ => none
  ofVal := .done
  coe_of_toVal_eq_some {e v} h := by cases e <;> simp_all
  toVal_coe _ := rfl
  primStep := RStep
  val_stuck h := by cases h <;> rfl

@[simp] theorem toVal_done (o : ROutcome) :
    ToVal.toVal (RExpr.done o) = some o := rfl

@[simp] theorem toVal_running (c : MCfg) :
    ToVal.toVal (RExpr.running c) = (none : Option ROutcome) := rfl

@[simp] theorem ofVal_eq (o : ROutcome) :
    (ToVal.ofVal o : RExpr) = RExpr.done o := rfl

/-! ## Step inversion — `stepFn` is a function, so the step is deterministic:
    the successor is pinned by whichever `StepResult` equation holds. -/

theorem step_next_inv {c : MCfg} {h : Heap} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .next m')
    {obs : List Empty} {e' : RExpr} {σ' : Heap} {efs : List RExpr}
    (hs : RStep (.running c, h) obs (e', σ', efs)) :
    σ' = m'.heap ∧ e' = .running m'.cfg ∧ efs = [] := by
  cases hs <;> simp_all

theorem step_val_inv {c : MCfg} {h : Heap} {v : Value} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .done v m')
    {obs : List Empty} {e' : RExpr} {σ' : Heap} {efs : List RExpr}
    (hs : RStep (.running c, h) obs (e', σ', efs)) :
    σ' = m'.heap ∧ e' = .done (.val v m'.heap) ∧ efs = [] := by
  cases hs <;> simp_all

theorem step_exc_inv {c : MCfg} {h : Heap} {e : Value} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .uncaught e m')
    {obs : List Empty} {e' : RExpr} {σ' : Heap} {efs : List RExpr}
    (hs : RStep (.running c, h) obs (e', σ', efs)) :
    σ' = m'.heap ∧ e' = .done (.exc e m'.heap) ∧ efs = [] := by
  cases hs <;> simp_all

/-! ## Reducibility (the lifting rules' safety side conditions) -/

theorem reducible_of_next {c : MCfg} {h : Heap} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .next m') :
    PrimStep.Reducible ((RExpr.running c), h) :=
  ⟨[], .running m'.cfg, m'.heap, [], RStep.next hf⟩

theorem reducible_of_val {c : MCfg} {h : Heap} {v : Value} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .done v m') :
    PrimStep.Reducible ((RExpr.running c), h) :=
  ⟨[], .done (.val v m'.heap), m'.heap, [], RStep.val hf⟩

theorem reducible_of_exc {c : MCfg} {h : Heap} {e : Value} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .uncaught e m') :
    PrimStep.Reducible ((RExpr.running c), h) :=
  ⟨[], .done (.exc e m'.heap), m'.heap, [], RStep.exc hf⟩

/-! ## Trace erasure: fuel-runner results are thread-pool traces (the
    golean/cerberus `steps_erased` analogue, fused with runner soundness —
    our runner IS `stepFn` iterated, so the two legs collapse into one). -/

open Language in
private theorem erased_next {c : MCfg} {h : Heap} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .next m') :
    ErasedStep (Expr := RExpr) ([.running c], h) ([.running m'.cfg], m'.heap) :=
  ⟨[], Language.Step.atomic (RStep.next hf) [] []⟩

open Language in
private theorem erased_val {c : MCfg} {h : Heap} {v : Value} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .done v m') :
    ErasedStep (Expr := RExpr) ([.running c], h) ([.done (.val v m'.heap)], m'.heap) :=
  ⟨[], Language.Step.atomic (RStep.val hf) [] []⟩

open Language in
private theorem erased_exc {c : MCfg} {h : Heap} {e : Value} {m' : Machine}
    (hf : Interp.stepFn (c.load h) = .uncaught e m') :
    ErasedStep (Expr := RExpr) ([.running c], h) ([.done (.exc e m'.heap)], m'.heap) :=
  ⟨[], Language.Step.atomic (RStep.exc hf) [] []⟩

open Language in
/-- A fuel run ending in a VALUE erases to a thread-pool trace from the
    split initial configuration to the terminal outcome. -/
theorem run_erased_val {fuel : Nat} {m : Machine} {v : Value} {m' : Machine}
    (hr : Interp.run fuel m = .value v m') :
    Relation.ReflTransGen (ErasedStep (Expr := RExpr))
      ([.running m.cfg], m.heap) ([.done (.val v m'.heap)], m'.heap) := by
  induction fuel generalizing m with
  | zero => simp [Interp.run] at hr
  | succ fuel ih =>
    rw [Interp.run] at hr
    cases hstep : Interp.stepFn m with
    | next m₂ =>
      rw [hstep] at hr
      exact .head (erased_next (m' := m₂) (by simpa using hstep)) (ih hr)
    | done v₂ m₂ =>
      rw [hstep] at hr
      cases hr
      exact .single (erased_val (by simpa using hstep))
    | uncaught e₂ m₂ => rw [hstep] at hr; cases hr
    | unsupported r => rw [hstep] at hr; cases hr
    | stuck msg => rw [hstep] at hr; cases hr

open Language in
/-- A fuel run ending in an UNCAUGHT exception erases likewise. -/
theorem run_erased_exc {fuel : Nat} {m : Machine} {e : Value} {m' : Machine}
    (hr : Interp.run fuel m = .uncaught e m') :
    Relation.ReflTransGen (ErasedStep (Expr := RExpr))
      ([.running m.cfg], m.heap) ([.done (.exc e m'.heap)], m'.heap) := by
  induction fuel generalizing m with
  | zero => simp [Interp.run] at hr
  | succ fuel ih =>
    rw [Interp.run] at hr
    cases hstep : Interp.stepFn m with
    | next m₂ =>
      rw [hstep] at hr
      exact .head (erased_next (m' := m₂) (by simpa using hstep)) (ih hr)
    | done v₂ m₂ => rw [hstep] at hr; cases hr
    | uncaught e₂ m₂ =>
      rw [hstep] at hr
      cases hr
      exact .single (erased_exc (by simpa using hstep))
    | unsupported r => rw [hstep] at hr; cases hr
    | stuck msg => rw [hstep] at hr; cases hr

end RubyCore.HJudge
