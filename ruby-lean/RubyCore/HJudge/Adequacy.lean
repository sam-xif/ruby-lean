/-
  RubyCore.HJudge.Adequacy — the exit theorem. An Iris WP against the
  whole-heap ownership discharges into a statement about the FUEL RUNNER —
  `RubyCore.Interp.run`, the exact function the difftest SUT executes — with
  Iris appearing only in the discharged hypothesis (the statement-TCB rule
  both sibling repos enforce).

  **Ported from `mdd/sorbet-lean/SorbetLean/Adequacy.lean`** (spike S1), with
  one in-tree simplification: the sibling package restated `typeErrorFamily`/
  `isTypeError` to keep its spine off the metatheory chain and carried a
  `ParityProbe.lean` to prove the restatements definitional. In-tree there is
  no package boundary, so this file imports `RubyCore.Proof.TypeSafety` and
  uses its predicates directly — the parity theorems collapse to the
  definitions themselves.

  Discharge chain (cerberus `RelSem/IrisAdequacy.lean` shape, one leg
  shorter — our runner IS `stepFn` iterated, so runner-soundness and trace
  erasure fused in `Lang.run_erased_*`):

    Hwp : stateIs h₀ ⊢ WP (running c₀) {{ o, ⌜φ o⌝ }}
      ⇒ iris-lean `ownP_adequacy`
      ⇒ adequate .NotStuck … (fun v _ => φ v)
      ⇒ per fuel-runner result: `run_erased_val`/`run_erased_exc` give the
        thread-pool trace, `adequate_result` fires
      ⇒ φ holds of every terminal runner outcome, at every fuel.

  House rules: no sorry, no new axioms.
-/
import Iris.ProgramLogic.OwnP
import RubyCore.HJudge.Rules
import RubyCore.Proof.TypeSafety

set_option autoImplicit false

namespace RubyCore.HJudge

open RubyCore
open Iris Iris.ProgramLogic

/-- The bad state as a terminal OUTCOME: an uncaught type-family exception.
    Mirrors `RubyCore.Proof.typeStuck` on `StepResult` (raised-then-rescued
    never reaches here — only escapes to toplevel produce an `.exc` outcome). -/
def typeStuckO : ROutcome → Prop
  | .exc e h => RubyCore.Proof.isTypeError h e
  | .val _ _ => False

/-- Statement parity with the metatheory's `StepResult`-level predicate,
    kernel-checked (the sibling's `ParityProbe`, collapsed): the outcome-level
    predicate agrees with `typeStuck` at every uncaught terminal. -/
theorem typeStuckO_parity (e : Value) (m : Machine) :
    typeStuckO (.exc e m.heap) ↔ RubyCore.Proof.typeStuck (.uncaught e m) :=
  Iff.rfl

/-! ## The exit theorem -/

/-- THE ADEQUACY THEOREM: a WP for the split configuration — provable at any
    functor bundle carrying the prerequisites — discharges into a pure
    statement about every terminal result of the fuel runner, at every fuel.
    (`unsupported`/`stuck`/`outOfFuel` results are not terminal outcomes and
    are not spoken about — the fragment gate's territory.) -/
theorem run_adequate_of_wp {GF : BundledGFunctors} [RubyGpreS GF]
    (c₀ : MCfg) (h₀ : Heap) (φ : ROutcome → Prop)
    (Hwp : ∀ [RubyGS GF],
      stateIs (GF := GF) h₀ ⊢
        WP (RExpr.running c₀) @ Stuckness.NotStuck ; ⊤ {{ o, ⌜φ o⌝ }}) :
    (∀ fuel v m', Interp.run fuel (c₀.load h₀) = .value v m' →
        φ (.val v m'.heap)) ∧
    (∀ fuel e m', Interp.run fuel (c₀.load h₀) = .uncaught e m' →
        φ (.exc e m'.heap)) := by
  have Had : adequate .NotStuck (RExpr.running c₀) h₀ (fun v _ => φ v) :=
    ownP_adequacy .NotStuck _ _ φ Hwp
  constructor
  · intro fuel v m' hr
    have htrace := run_erased_val (fuel := fuel) hr
    simp only [cfg_load, heap_load] at htrace
    exact Had.adequate_result [] m'.heap (.val v m'.heap) htrace
  · intro fuel e m' hr
    have htrace := run_erased_exc (fuel := fuel) hr
    simp only [cfg_load, heap_load] at htrace
    exact Had.adequate_result [] m'.heap (.exc e m'.heap) htrace

/-- THE SAFETY COROLLARY (Iris-free conclusion): a WP whose postcondition
    excludes type-stuck outcomes means NO run of the program — at any fuel —
    ends in an uncaught type-family exception. -/
theorem noTypeStuck_of_wp {GF : BundledGFunctors} [RubyGpreS GF]
    (c₀ : MCfg) (h₀ : Heap)
    (Hwp : ∀ [RubyGS GF],
      stateIs (GF := GF) h₀ ⊢
        WP (RExpr.running c₀) @ Stuckness.NotStuck ; ⊤
          {{ o, ⌜¬ typeStuckO o⌝ }}) :
    ∀ fuel e m', Interp.run fuel (c₀.load h₀) = .uncaught e m' →
      ¬ RubyCore.Proof.isTypeError m'.heap e := by
  intro fuel e m' hr
  exact (run_adequate_of_wp c₀ h₀ (fun o => ¬ typeStuckO o) Hwp).2 fuel e m' hr

end RubyCore.HJudge
