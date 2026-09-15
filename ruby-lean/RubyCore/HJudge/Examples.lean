/-
  RubyCore.HJudge.Examples — worked ends, one per admission route.

  * `ofJudge`: the Sound.lean examples upgraded to denotation conclusions —
    including the J31 lambda pilot and the J35 `define_method` pilot, whose
    `Judge` derivations carry semantic-axiom leaves; the H-layer consumes
    them unchanged. Each gains a conclusion the first-order layer could not
    phrase: the machine's own `is_a?` at the run's final heap.
  * `sub`: `Ty.bool`'s meaning, finally said — `T::Boolean` is
    `TrueClass ∪ FalseClass`, and each half sits below the union.
  * `wp`, abstract: `true` types at `HTy.trueClass` in EVERY environment —
    a two-step walk from an arbitrary conformant state (the constructor's
    quantifier), at a type `Ty` cannot express (`Ty.bool` covers both
    halves; nothing covers one).
  * the closed Iris route: `(1).zero?` walked concretely from the boot
    machine by `rb_walk` (the sibling's replay move), landed on
    `ReachableResult` at `HTy.falseClass` — finer than the fragment's
    `Ty.bool`, certified by execution-in-the-logic.
  * `HTy.duck`: the behavioral door, exercised at the boot heap.

  House rules: no sorry, no new axioms.
-/
import RubyCore.HJudge.Judge
import RubyCore.HJudge.EvalSet
import RubyCore.Proof.Judgment.SemAxiom
import RubyCore.Proof.Judgment.Rails

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RubyCore.HJudge

open RubyCore
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof
open RubyCore.Proof.Judgment
open Interp
open Iris Iris.ProgramLogic

/-! ## `ofJudge` — the Sound.lean examples, at denotations -/

/-- `x = 1; if true then x else 0 end` — judged at `⟦Integer⟧`. -/
theorem egIf_hJudged :
    HJudge [] (declsOf Static.egIf) [] Static.egIf Proof.Judgment.topJCtx HTy.integer :=
  .ofJudge egIf_mfrag (by decide) egIf_judged rfl

/-- ... and the denotation conclusion: every terminating run's value passes
    the machine's own `is_a?(Integer)` AT THE FINAL HEAP — the statement
    `VTy` approximated and `HTy.den` says outright. -/
theorem egIf_result_isA :
    ∀ v mf, ReachableResult (Machine.init Static.egIf) (.done v mf) →
      isA mf.heap v Boot.integerId = true :=
  fun v mf hr =>
    hJudge_result_den semAxiomsOk_nil declsOkJ_declsOf egIf_hJudged v mf hr

/-- `(1 + 2).zero?` — `Ty.bool` bridges to the union it always meant. -/
theorem egZero_hJudged :
    HJudge [] (declsOf Static.egZero) [] Static.egZero Proof.Judgment.topJCtx HTy.boolean :=
  .ofJudge egZero_mfrag (by decide) egZero_judged rfl

/-- The J31 pilot (`x = 1; lambda { 1 }; x`): the derivation's `semantic`
    leaf rides into the H-layer unchanged — same axioms `A`, same obligation
    `SemAxiomsOk [lamClaim]`, discharged once by executing the semantics. -/
theorem egSem_hJudged :
    HJudge [lamClaim] (declsOf egSem) [] egSem Proof.Judgment.topJCtx HTy.integer :=
  .ofJudge egSem_mfrag (by decide) egSem_judged rfl

theorem egSem_result_isA :
    ∀ v mf, ReachableResult (Machine.init egSem) (.done v mf) →
      isA mf.heap v Boot.integerId = true :=
  fun v mf hr =>
    hJudge_result_den semAxiomsOk_lam declsOkJ_declsOf egSem_hJudged v mf hr

/-- The J35 pilot (`class String; define_method(:shout) { 1 }; end;
    "a".shout`): real metaprogramming, judged at a denotation. The final
    heap this `isA` reads CONTAINS the `define_method`-installed row — the
    denotation is heap-indexed, so the claim is about the mutated world,
    not the boot one. -/
theorem railsE_hJudged :
    HJudge [dmClaim] (declsOf railsE) [] railsE Proof.Judgment.topJCtx HTy.integer :=
  .ofJudge railsE_mfrag (by decide) railsE_judged rfl

theorem railsE_result_isA :
    ∀ v mf, ReachableResult (Machine.init railsE) (.done v mf) →
      isA mf.heap v Boot.integerId = true :=
  fun v mf hr =>
    hJudge_result_den semAxiomsOk_dm declsOkJ_declsOf railsE_hJudged v mf hr

/-! ## `sub` — semantic subsumption -/

/-- Widening into a nilable, by denotation inclusion. -/
theorem egIf_hJudged_nilable :
    HJudge [] (declsOf Static.egIf) [] Static.egIf Proof.Judgment.topJCtx
      (.nilable HTy.integer) :=
  egIf_hJudged.sub (HSub.le_nilable _)

/-- Everything sits below the gradual top. -/
theorem egIf_hJudged_untyped :
    HJudge [] (declsOf Static.egIf) [] Static.egIf Proof.Judgment.topJCtx .untyped :=
  egIf_hJudged.sub (HSub.le_untyped _)

/-! ## `wp`, abstract — `true : TrueClass`, in every environment

The two-step walk from an ARBITRARY conformant state: `Conformant` pins the
continuation empty, `evalExpr` reduces on the expression alone, and the
denotation lemmas are heap-generic — so the walk never needs to know the
heap. `Ty` cannot state this type at all (`Ty.bool` is the union). -/

/-- The WP, per conformant-shaped state (only `ctl`/`kont` matter). -/
theorem tru_wp {GF : BundledGFunctors} [RubyGS GF] {m : Machine}
    (hctl : m.ctl = .eval .tru) (hkont : m.kont = []) :
    stateIs (GF := GF) m.heap ⊢
      WP (RExpr.running m.cfg) @ Stuckness.NotStuck ; ⊤
        {{ o, ⌜HOutcomeOk HTy.trueClass o⌝ }} := by
  refine wp_walk_step (m' := withCtl m (.value (.bool true))) ?_ ?_
  · show Interp.stepFn m = .next (withCtl m (.value (.bool true)))
    rw [Interp.stepFn, hctl]
    rfl
  · refine wp_walk_val (v := .bool true)
      (m' := withCtl m (.value (.bool true))) ?_ ?_
    · show Interp.stepFn (withCtl m (.value (.bool true))) =
        .done (.bool true) (withCtl m (.value (.bool true)))
      simp only [Interp.stepFn, withCtl, Interp.applyKont, hkont]
    · exact HTy.den_true _

/-- The judgment — at every `A`, `D`, `Γ`, `c`: the walk needed nothing else. -/
theorem tru_hJudged (A : SemAxioms) (D : Decls) (Γ : Env) (c : JCtx) :
    HJudge A D Γ .tru c HTy.trueClass := by
  refine .wp ?_
  intro m hconf hctl GF _
  obtain ⟨-, -, -, -, -, -, hkont, -⟩ := hconf
  exact tru_wp hctl hkont

/-- Closed: every terminating run of `true` is a `TrueClass` instance at its
    final heap. -/
theorem tru_result_isA :
    ∀ v mf, ReachableResult (Machine.init .tru) (.done v mf) →
      isA mf.heap v Boot.trueClassId = true :=
  fun v mf hr =>
    hJudge_result_den semAxiomsOk_nil declsOkJ_declsOf
      (tru_hJudged [] (declsOf .tru) [] Proof.Judgment.topJCtx) v mf hr

/-! ## The closed Iris route — `(1).zero?` at `FalseClass`, by `rb_walk`

The sibling's replay move, landed on the judgment layer's ground truth: a
concrete machine walk in the logic (every step a `stepFn` equation), the
postcondition at a type FINER than the fragment's `Ty.bool` (`1.zero?` is
`false`, and `HTy.falseClass` says so), discharged through `wp_machine_sound`
onto `ReachableResult`. -/

/-- `(1).zero?` -/
def oneZeroE : Expr := .send (some (.int 1)) "zero?" [] none

set_option maxHeartbeats 400000000 in
/-- The concrete walk from the boot machine. -/
theorem oneZero_wp {GF : BundledGFunctors} [RubyGS GF] :
    stateIs (GF := GF) (Machine.init oneZeroE).heap ⊢
      WP (RExpr.running (Machine.init oneZeroE).cfg) @ Stuckness.NotStuck ; ⊤
        {{ o, ⌜HOutcomeOk HTy.falseClass o⌝ }} := by
  rb_walk
  exact HTy.den_false _

/-- ... landed on the small-step closure: every terminating run of
    `(1).zero?` is a `FalseClass` instance. `Ty` tops out at `bool` here;
    the denotation does not. -/
theorem oneZero_result_isA :
    ∀ v mf, ReachableResult (Machine.init oneZeroE) (.done v mf) →
      isA mf.heap v Boot.falseClassId = true :=
  fun v mf hr =>
    (wp_machine_sound (Machine.init oneZeroE) (HOutcomeOk HTy.falseClass)
      (fun _GF _ => oneZero_wp)).1 v mf hr

/-! ## The behavioral door, exercised -/

/-- A duck type is a denotation TODAY: `5` responds to `+` and `zero?` at the
    boot heap, by the machine's own `lookup`. -/
example : (HTy.duck ["+", "zero?"]).den Boot.initHeap (.int 5) := by
  simp only [HTy.duck, HTy.den]
  decide

/-- ... and refuses what the heap refuses. -/
example : ¬ (HTy.duck ["frobnicate"]).den Boot.initHeap (.int 5) := by
  simp only [HTy.duck, HTy.den]
  decide

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.HJudge.egIf_result_isA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egIf_result_isA

/-- info: 'RubyCore.HJudge.railsE_result_isA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms railsE_result_isA

/-- info: 'RubyCore.HJudge.tru_result_isA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tru_result_isA

/-- info: 'RubyCore.HJudge.oneZero_result_isA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oneZero_result_isA

end RubyCore.HJudge
