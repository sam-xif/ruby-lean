/-
  RubyCore.HJudge.Judge — the judgment `HJudge`, its four admission routes,
  and type safety through it (the SemJudge/Judge formula, one rung up).

  The shape mirrors J30/J31 exactly:

    HJudge  — an inductive whose constructors are the ADMISSION ROUTES into
              the semantic judgment: the syntactic route (`ofJudge`, a
              `Judge` derivation bridged through `HTy.ofTy?`), the direct
              semantic route (`sem`, an `HSemJudge` proved by hand — the J31
              admission, one rung up), the Iris route (`wp`, a weakest
              precondition over the seat, discharged per conformant state),
              and semantic subsumption (`sub`, denotation inclusion).
    hJudge_semJudge — the fundamental lemma: every route lands in
              `HSemJudge`. The `ofJudge` case is `judge_semJudge` (the paid
              preservation mountain) composed with the bridge; the `wp` case
              is the seat's adequacy composed with the run↔reachability
              erasure below; `sem` is identity; `sub` is `HSub`.
    hJudge_sound / hJudge_result_den — type safety and result typing at the
              boot table, `semJudge_sound`'s shape verbatim.

  The run↔reachability erasure (`run_lift_of_reaches`) is the one genuinely
  new metatheoretic fact: the seat's adequacy lands on the fuel runner
  (`Interp.run`, the difftest SUT's function), the judgment layer's ground
  truth is the small-step closure (`ReachableResult`) — and the two agree
  because the runner IS `stepFn` iterated, so a reachable terminal is a
  finite-fuel run.

  House rules: no sorry, no new axioms.
-/
import RubyCore.HJudge.Sem
import RubyCore.HJudge.Adequacy

set_option autoImplicit false

namespace RubyCore.HJudge

open RubyCore
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof
open RubyCore.Proof.Judgment
open Interp
open Iris Iris.ProgramLogic

/-! ## Reachable terminals are finite-fuel runs -/

/-- Lift a run equation backwards along the small-step closure: whatever some
    fuel produces from a reached machine, some fuel produces from the start. -/
private theorem run_lift_of_reaches {m₀ m' : Machine} (hr : Reaches m₀ m')
    {res : Interp.RunResult} :
    ∀ {fuel : Nat}, Interp.run fuel m' = res →
      ∃ fuel', Interp.run fuel' m₀ = res := by
  induction hr with
  | refl => exact fun h => ⟨_, h⟩
  | tail hr' hstep ih =>
    intro fuel hres
    exact ih (fuel := fuel + 1) (by rw [Interp.run, hstep]; exact hres)

/-- A reachable `done` terminal is a finite-fuel `.value` run. -/
theorem run_of_reachable_done {m₀ : Machine} {v : Value} {mf : Machine}
    (hr : ReachableResult m₀ (.done v mf)) :
    ∃ fuel, Interp.run fuel m₀ = .value v mf := by
  obtain ⟨m', hreach, hstep⟩ := hr
  exact run_lift_of_reaches hreach (fuel := 1) (by rw [Interp.run, hstep])

/-- A reachable `uncaught` terminal is a finite-fuel `.uncaught` run. -/
theorem run_of_reachable_uncaught {m₀ : Machine} {e : Value} {mf : Machine}
    (hr : ReachableResult m₀ (.uncaught e mf)) :
    ∃ fuel, Interp.run fuel m₀ = .uncaught e mf := by
  obtain ⟨m', hreach, hstep⟩ := hr
  exact run_lift_of_reaches hreach (fuel := 1) (by rw [Interp.run, hstep])

/-! ## The WP postcondition shape, and adequacy landed on `ReachableResult` -/

/-- The outcome postcondition an H-typed WP carries: a value outcome inhabits
    the denotation at the final heap; an exception outcome is not a
    type-family error (it may be a *raise* — `SemJudge`'s safety half makes
    exactly the same allowance through `typeStuck`). -/
def HOutcomeOk (τh : HTy) : ROutcome → Prop
  | .val v h => τh.den h v
  | .exc e h => ¬ RubyCore.Proof.isTypeError h e

/-- **Adequacy, landed on the small-step closure**: a WP at a machine's split
    configuration constrains every reachable terminal of that machine — the
    seat's `run_adequate_of_wp` composed with the run↔reachability erasure.
    Stated at any `φ`; the H-layer instantiates `φ := HOutcomeOk τh`. -/
theorem wp_machine_sound (m₀ : Machine) (φ : ROutcome → Prop)
    (Hwp : ∀ (GF : BundledGFunctors) [RubyGS GF],
      stateIs (GF := GF) m₀.heap ⊢
        WP (RExpr.running m₀.cfg) @ Stuckness.NotStuck ; ⊤ {{ o, ⌜φ o⌝ }}) :
    (∀ v mf, ReachableResult m₀ (.done v mf) → φ (.val v mf.heap)) ∧
    (∀ e mf, ReachableResult m₀ (.uncaught e mf) → φ (.exc e mf.heap)) := by
  have had := run_adequate_of_wp (GF := RubyS) m₀.cfg m₀.heap φ
    (fun {_} => Hwp RubyS)
  constructor
  · intro v mf hr
    obtain ⟨fuel, hrun⟩ := run_of_reachable_done hr
    exact had.1 fuel v mf (by simpa using hrun)
  · intro e mf hr
    obtain ⟨fuel, hrun⟩ := run_of_reachable_uncaught hr
    exact had.2 fuel e mf (by simpa using hrun)

/-- The Iris admission: a WP per conformant state yields the semantic
    judgment. This is the direction the seat can supply (a WP is *stronger*
    than the reachability claim); the converse — manufacturing a WP from an
    invariant — is the recorded Löb-induction rung, not needed for soundness. -/
theorem hsem_of_wp {A : SemAxioms} {D : Decls} {Γ : Env} {e : Expr} {c : JCtx}
    {τh : HTy}
    (hwp : ∀ m : Machine, Conformant A D c Γ m → m.ctl = .eval e →
      ∀ (GF : BundledGFunctors) [RubyGS GF],
        stateIs (GF := GF) m.heap ⊢
          WP (RExpr.running m.cfg) @ Stuckness.NotStuck ; ⊤
            {{ o, ⌜HOutcomeOk τh o⌝ }}) :
    HSemJudge A D Γ e c τh := by
  intro m hconf hctl
  have hws := wp_machine_sound m (HOutcomeOk τh) (hwp m hconf hctl)
  constructor
  · intro r hr hstuck
    cases r with
    | uncaught exc mf => exact hws.2 exc mf hr hstuck
    | next m' => exact hstuck
    | done v mf => exact hstuck
    | unsupported s => exact hstuck
    | stuck s => exact hstuck
  · intro v mf hr
    exact hws.1 v mf hr

/-! ## The judgment -/

/-- **`HJudge A D Γ e c τh`** — the H-layer judgment: `e`, in environment `Γ`
    at context `c` over table `D` (with semantic axioms `A`), semantically
    types at the denotation `τh`. The constructors are the admission routes;
    nothing else is one. -/
inductive HJudge (A : SemAxioms) (D : Decls) (Γ : Env) (e : Expr) (c : JCtx) :
    HTy → Prop where
  /-- The syntactic route: a `Judge` derivation, bridged. Everything the
      first-order pipeline can certify — including J31/J35 semantic-axiom
      leaves inside the derivation — arrives here. -/
  | ofJudge {τ : Ty} {τh : HTy} {Γ' : Env} {D' : Decls}
      (hmf : MFrag A e) (hfr : fragHead e = true)
      (hj : Judge A D Γ e true c τ Γ' D')
      (ht : HTy.ofTy? τ = some τh) : HJudge A D Γ e c τh
  /-- The direct semantic route: an `HSemJudge` proved by any means — the
      J30 extension point, at denotation types. -/
  | sem {τh : HTy} (hs : HSemJudge A D Γ e c τh) : HJudge A D Γ e c τh
  /-- The Iris route: a weakest precondition over the seat, per conformant
      state. The walk tactics (`rb_walk`) discharge these where the state is
      concrete enough to step. -/
  | wp {τh : HTy}
      (hwp : ∀ m : Machine, Conformant A D c Γ m → m.ctl = .eval e →
        ∀ (GF : BundledGFunctors) [RubyGS GF],
          stateIs (GF := GF) m.heap ⊢
            WP (RExpr.running m.cfg) @ Stuckness.NotStuck ; ⊤
              {{ o, ⌜HOutcomeOk τh o⌝ }}) : HJudge A D Γ e c τh
  /-- Semantic subsumption: denotation inclusion, at every heap. -/
  | sub {σh τh : HTy} (hσ : HJudge A D Γ e c σh) (hs : HSub σh τh) :
      HJudge A D Γ e c τh

/-! ## The fundamental lemma, and type safety -/

/-- **The fundamental lemma (adequacy of `HJudge`)**: every admission route
    lands in the semantic judgment. -/
theorem hJudge_semJudge {A : SemAxioms} {D : Decls} {Γ : Env} {e : Expr}
    {c : JCtx} {τh : HTy}
    (hax : SemAxiomsOk A) (hj : HJudge A D Γ e c τh) :
    HSemJudge A D Γ e c τh := by
  induction hj with
  | ofJudge hmf hfr hjd ht => exact semJudge_toH (judge_semJudge hax hmf hfr hjd) ht
  | sem hs => exact hs
  | wp hwp => exact hsem_of_wp hwp
  | sub hσ hs ih =>
    intro m hconf hctl
    obtain ⟨hsafe, hres⟩ := ih m hconf hctl
    exact ⟨hsafe, fun v mf hr => hs mf.heap v (hres v mf hr)⟩

/-- **Type safety from the semantic judgment alone** — `semJudge_sound`'s
    statement, at the H-layer. -/
theorem hSemJudge_sound {A : SemAxioms} {p : Expr} {F : Decls} {τh : HTy}
    (hD : DeclsOkJ A F Boot.initHeap)
    (hs : HSemJudge A F [] p topJCtx τh) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  (hs _ (conformant_init hD) rfl).1

/-- **Type safety through the judgment**: the composition
    `HJudge → HSemJudge → safety`. -/
theorem hJudge_sound {A : SemAxioms} {p : Expr} {F : Decls} {τh : HTy}
    (hax : SemAxiomsOk A)
    (hD : DeclsOkJ A F Boot.initHeap)
    (hj : HJudge A F [] p topJCtx τh) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  hSemJudge_sound hD (hJudge_semJudge hax hj)

/-- **Result typing in the denotation**: a judged program's terminating value
    inhabits `τh.den` at the final heap — for `τh := HTy.cls c` this is the
    machine's own `is_a?` at the run's end, a statement the first-order layer
    could not even phrase. -/
theorem hJudge_result_den {A : SemAxioms} {p : Expr} {F : Decls} {τh : HTy}
    (hax : SemAxiomsOk A)
    (hD : DeclsOkJ A F Boot.initHeap)
    (hj : HJudge A F [] p topJCtx τh) :
    ∀ v mf, ReachableResult (Machine.init p) (.done v mf) →
      τh.den mf.heap v :=
  fun v mf hr =>
    (hJudge_semJudge hax hj _ (conformant_init hD) rfl).2 v mf hr

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.HJudge.hJudge_semJudge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hJudge_semJudge

/-- info: 'RubyCore.HJudge.hJudge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hJudge_sound

/-- info: 'RubyCore.HJudge.hJudge_result_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hJudge_result_den

/-- info: 'RubyCore.HJudge.wp_machine_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wp_machine_sound

end RubyCore.HJudge
