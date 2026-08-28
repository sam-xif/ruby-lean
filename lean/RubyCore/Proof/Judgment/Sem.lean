import RubyCore.Proof.Judgment.Sound

/-!
# `SemJudge` (J30) — the semantic judgment, and `Judge`'s adequacy against it

`judgment-layer.md` §1.5 records the fully semantic grounding ("the truly semantic
type of an expression is the set of (heap, value) pairs it can evaluate to") and
declines to buy step-indexing for it because **the reachability property is already
the semantic ground truth**. This file cashes that sentence into a definition: the
semantic judgment *is* a reachability claim.

    SemJudge D Γ e c τ  :=  in every machine state conformant with (D, Γ, c),
                            running e (a) reaches no type-stuck outcome and
                            (b) every terminating run's value inhabits τ (`VTy`)

Note what the definiens does **not** mention: `Judge`, `MFrag`, `KontOkJ`, or any
checker — only the machine (`ReachableResult`), the Judge-free heap/frame conjuncts
(`Conformant`), and the value judgment (`VTy`). That makes `SemJudge` the layer's
**extension point**: a construct the syntactic fragment cannot check (a builtin
pattern, a metaprogrammed method, a Rails-generated row) can be admitted by proving
its `SemJudge` statement *directly* — by execution, by a conformance lemma, by hand —
and it composes with syntactically-checked code because the syntactic route is
itself only a way of manufacturing `SemJudge` facts:

* `judge_semJudge` — **the fundamental lemma / adequacy of the syntactic system**:
  a `Judge` derivation yields the semantic judgment. Its content is the already-paid
  preservation mountain (`step_okJ`), repackaged through the J29 answer-typed
  invariant; the lemma itself is assembly.
* `semJudge_sound` — type safety composed *through* the semantic judgment: a
  `SemJudge` at the boot table certifies the reachability property, whatever
  supplied the `SemJudge`.
* `judge_result_vty` — the capability J29 bought: a judged program's terminating
  value inhabits the judged type, machine-checked end to end. Pre-J29 the invariant
  forgot the answer type (`KontOkJ.nil` closed at any in-flight type), so this was
  true and unprovable.

The named bills, deliberately not paid here (each a recorded rung, none blocked):
the out-environment `Γ'` and out-table `D'` are **not** in `SemJudge` — recovering
them needs the final frame's conformance threaded to the `done` step the way `ans`
now is (same trick, one more parameter), and nothing consumes them yet; and the
first *directly-proved* `SemJudge` fact (the extension pilot — a `define_method`d
row admitted semantically) is the natural next rung, J31.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

set_option maxRecDepth 100000

/-! ## The conformant start state

Every `InvJ` conjunct that mentions **no typing derivation** — the heap facts, the
frame/stack conformance at the claimed environment, the globals — plus an empty
continuation (the judgment speaks about running `e` *to completion*) and a context
whose jump channels are closed (`ret`/`inLoop` none: `e` is not mid-method,
mid-loop — those channels are what `KontOkJ.nil` refutes at the empty position). -/

/-- A machine state conformant with table `D`, environment `Γ`, and context `c`:
    the Judge-free half of `InvJ`, at an empty continuation. -/
def Conformant (A : SemAxioms) (D : Decls) (c : JCtx) (Γ : Env) (m : Machine) : Prop :=
  NoHook m.heap ∧ Saturated m.heap ∧ ChainsIn m.heap ∧ LitClsOk m.heap ∧ ClassOk m.heap ∧
  BottomObj m.frames m.stack ∧
  m.kont = [] ∧
  framePopLabels m.kont = m.stack.dropLast ∧
  ClosuresOk m ∧
  DeclsOkJ A D m.heap ∧
  FramesOkJ m.heap m.frames m.stack [Γ] ∧
  StackCtx m.heap m.frames m.stack (jctxs c []) ∧
  GlobalsOk D m.heap m.globals ∧
  c.ret = none ∧ c.inLoop = none

/-! ## The semantic judgment -/

/-- **`SemJudge D Γ e c τ`** — the semantic typing judgment: in every conformant
    state, `e` runs type-safely and a terminating run's value inhabits `τ`.

    Defined by reachability alone. `Judge` does not appear; neither does `MFrag`
    (the fragment gate is a property of the *syntactic* route, not of the meaning —
    an out-of-fragment construct can still satisfy `SemJudge`, which is the whole
    point of having it). -/
def SemJudge (A : SemAxioms) (D : Decls) (Γ : Env) (e : Expr) (c : JCtx) (τ : Ty) : Prop :=
  ∀ m : Machine, Conformant A D c Γ m → m.ctl = .eval e →
    (∀ r, ReachableResult m r → ¬ typeStuck r) ∧
    (∀ v mf, ReachableResult m (.done v mf) → VTy mf.heap v τ)

/-! ## Adequacy: the syntactic judgment is sound for the semantic one -/

/-- A conformant state holding a judged `e` satisfies the answer-typed invariant —
    `initiationJ` generalized from the boot machine to any conformant state, with
    the answer type pinned at the judged `τ` (J29). -/
theorem invJ_of_conformant {A : SemAxioms} {D : Decls} {c : JCtx} {Γ : Env}
    {m : Machine} {e : Expr} {τ : Ty} {Γ' : Env} {D' : Decls}
    (hconf : Conformant A D c Γ m) (hctl : m.ctl = .eval e)
    (hmf : MFrag A e) (hfr : fragHead e = true)
    (hj : Judge A D Γ e true c τ Γ' D') :
    InvJ τ A m := by
  obtain ⟨hh, hsat, hchn, hstr, hcls, hbot, hk0, hks, hclo, htab, hfs, hsc, hgl,
    hret, hloop⟩ := hconf
  refine ⟨hh, hsat, hchn, hstr, hcls, hbot, hks, hclo, D, c, Γ, [], htab, hfs, hsc,
    hgl, ?_⟩
  unfold CtlOkJ
  rw [hctl]
  refine Or.inl ⟨hfr, hmf, τ, τ, Γ', D', Γ', hj, SubJ.refl τ, SubEnv.refl Γ', ?_⟩
  rw [hk0]
  exact KontOkJ.nil (SubJ.refl τ)
    (fun cΓ Γs' hEq => by cases hEq; exact hret)
    (fun cΓ Γs' hEq => by cases hEq; exact hloop)

/-- The J29 `done` payoff, shaped for `invariant_result_sound`: whatever `StepOkJ`
    knows of a step result, restricted to the `done` arm. -/
def DoneVTy (τ : Ty) : StepResult → Prop
  | .done v mf => VTy mf.heap v τ
  | _ => True

theorem stepOkJ_doneVTy {ans : Ty} {A : SemAxioms} {r : StepResult} (h : StepOkJ ans A r) :
    DoneVTy ans r := by
  cases r <;> first | trivial | exact h

/-- **The fundamental lemma (adequacy of `Judge`)**: a derivation yields the
    semantic judgment. The safety half is `invariant_sound_from` at the answer-typed
    invariant; the result half is `invariant_result_sound` reading `StepOkJ`'s J29
    `done` arm. All the content is `step_okJ` — this proof is assembly. -/
theorem judge_semJudge {A : SemAxioms} {D : Decls} {Γ : Env} {e : Expr} {c : JCtx}
    {τ : Ty} {Γ' : Env} {D' : Decls}
    (hax : SemAxiomsOk A)
    (hmf : MFrag A e) (hfr : fragHead e = true)
    (hj : Judge A D Γ e true c τ Γ' D') :
    SemJudge A D Γ e c τ := by
  intro m hconf hctl
  have hinv : InvJ τ A m := invJ_of_conformant hconf hctl hmf hfr hj
  refine ⟨invariant_sound_from (InvJ τ A) hinv (consecutionJ hax) (safetyJ hax), ?_⟩
  intro v mf hr
  exact invariant_result_sound (InvJ τ A) hinv (consecutionJ hax)
    (fun m' hm' => stepOkJ_doneVTy (step_okJ hax hm')) (.done v mf) hr

/-! ## Type safety through the semantic judgment -/

/-- The boot machine is conformant at the boot table and top context — the
    heap-side facts of `initiationJ`, verbatim (computations on a literal heap). -/
theorem conformant_init {A : SemAxioms} {p : Expr} {F : Decls}
    (hD : DeclsOkJ A F Boot.initHeap) :
    Conformant A F topJCtx [] (Machine.init p) := by
  refine ⟨
    (show NoHook (Machine.init p).heap from
      noHookB_sound (by decide : noHookB Boot.initHeap = true)),
    (show Saturated (Machine.init p).heap from
      saturatedB_sound (by decide : saturatedB Boot.initHeap = true)),
    (show ChainsIn (Machine.init p).heap from chainsIn_initHeap),
    (show LitClsOk (Machine.init p).heap from
      ⟨⟨(by decide : (Boot.initHeap.classPayload? Boot.stringId).isSome = true),
        (by rfl : className Boot.initHeap Boot.stringId = "String")⟩,
       ⟨(by decide : (Boot.initHeap.classPayload? Boot.arrayId).isSome = true),
        (by rfl : className Boot.initHeap Boot.arrayId = "Array")⟩,
       (by decide : (Boot.initHeap.classPayload? Boot.procId).isSome = true),
       (by decide : (Boot.initHeap.classPayload? Boot.hashId).isSome = true),
       ⟨(by decide : (Boot.initHeap.classPayload? Boot.regexpId).isSome = true),
        (by rfl : className Boot.initHeap Boot.regexpId = "Regexp")⟩⟩),
    (show ClassOk (Machine.init p).heap from classOk_initHeap),
    (show BottomObj (Machine.init p).frames (Machine.init p).stack by
      simp [Machine.init, Machine.initOn, BottomObj]),
    rfl,
    (by simp [Machine.init, Machine.initOn, framePopLabels]),
    (by intro κ hm; simp [Machine.init, Machine.initOn] at hm),
    hD, ?_, ?_,
    (fun x pr σ _ hf _ => absurd hf (by simp [Machine.init, Machine.initOn])),
    rfl, rfl⟩
  · show FramesOkJ (Machine.init p).heap (Machine.init p).frames
      (Machine.init p).stack [[]]
    simp [Machine.init, Machine.initOn, FramesOkJ, FrameConformsJ, ShallowChain, envGet?]
    decide
  · show StackCtx (Machine.init p).heap (Machine.init p).frames
      (Machine.init p).stack (jctxs topJCtx [])
    refine ⟨?_, ?_, ?_, ?_, ?_, Or.inr rfl, fun mn h => absurd h (by simp [topJCtx]),
      fun _ => rfl, (fun hcb _ => nomatch hcb), (fun hmb _ => nomatch hmb),
      (fun hfc _ => nomatch hfc), trivial⟩
    · show (Boot.initHeap.classPayload? Boot.objectId).isSome = true
      decide
    · exact fun _ => (show ClassOk (Machine.init p).heap from
        classOkB_sound (by decide : classOkB Boot.initHeap = true)).1
    · exact fun hz => absurd rfl hz
    · exact fun sc hsc => absurd hsc (by simp [topJCtx, jctxs])
    · simp [Machine.init, Machine.initOn, Array.getD]

/-- **Type safety from the semantic judgment alone.** Note the hypothesis: any
    `SemJudge`, however obtained — a `Judge` derivation via `judge_semJudge`, or a
    future direct semantic proof of a construct the fragment cannot check. -/
theorem semJudge_sound {A : SemAxioms} {p : Expr} {F : Decls} {τ : Ty}
    (hD : DeclsOkJ A F Boot.initHeap)
    (hs : SemJudge A F [] p topJCtx τ) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  (hs _ (conformant_init hD) rfl).1

/-- `judge_sound`, re-derived **through** the semantic judgment — the composition
    `Judge → SemJudge → safety` factoring where the pre-J30 route went
    `Judge → InvJ → safety` directly. Same conclusion; the middle layer is now a
    stated object rather than an implicit path. -/
theorem judge_sound_via_sem {A : SemAxioms} {p : Expr} {F : Decls} {τ : Ty}
    {Γ' : Env} {D' : Decls}
    (hax : SemAxiomsOk A)
    (hD : DeclsOkJ A F Boot.initHeap)
    (hmf : MFrag A p)
    (hfr : fragHead p = true)
    (hj : Judge A F [] p true topJCtx τ Γ' D') :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  semJudge_sound hD (judge_semJudge hax hmf hfr hj)

/-- **Result typing** — the new capability: a judged program's terminating value
    inhabits the judged type. Unprovable before J29 (the invariant's existentials
    re-closed `KontOkJ.nil` at whatever type arrived). -/
theorem judge_result_vty {A : SemAxioms} {p : Expr} {F : Decls} {τ : Ty} {Γ' : Env}
    {D' : Decls}
    (hax : SemAxiomsOk A)
    (hD : DeclsOkJ A F Boot.initHeap)
    (hmf : MFrag A p)
    (hfr : fragHead p = true)
    (hj : Judge A F [] p true topJCtx τ Γ' D') :
    ∀ v mf, ReachableResult (Machine.init p) (.done v mf) → VTy mf.heap v τ :=
  fun v mf hr =>
    (judge_semJudge hax hmf hfr hj _ (conformant_init hD) rfl).2 v mf hr

/-! ## Worked ends — the Sound.lean examples, upgraded

Each existing example's safety theorem re-derives through `SemJudge`, and each
gains the result-typing conclusion its derivation always promised. -/

/-- `x = 1; if true then x else 0 end` terminates in an `Integer` — every
    terminating run, machine-checked, not just the one `run` exhibits. -/
theorem egIf_result_int :
    ∀ v mf, ReachableResult (Machine.init Static.egIf) (.done v mf) →
      VTy mf.heap v .int :=
  judge_result_vty semAxiomsOk_nil declsOkJ_declsOf egIf_mfrag (by decide) egIf_judged

/-- `(1 + 2).zero?` terminates in a `Boolean` — through two `baseDecls` rows. -/
theorem egZero_result_bool :
    ∀ v mf, ReachableResult (Machine.init Static.egZero) (.done v mf) →
      VTy mf.heap v .bool :=
  judge_result_vty semAxiomsOk_nil declsOkJ_declsOf egZero_mfrag (by decide) egZero_judged

/-- The user-method flagship (`class String; def shout; 1; end; "x".shout; end`)
    terminates in an `Integer` — the promoted row's return type, delivered. -/
theorem egUserCall_result_int :
    ∀ v mf, ReachableResult (Machine.init Static.egUserCall) (.done v mf) →
      VTy mf.heap v .int :=
  judge_result_vty semAxiomsOk_nil declsOkJ_declsOf egUserCall_mfrag (by decide) egUserCall_judged

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.Proof.Judgment.judge_semJudge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms judge_semJudge

/-- info: 'RubyCore.Proof.Judgment.semJudge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semJudge_sound

/-- info: 'RubyCore.Proof.Judgment.judge_sound_via_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms judge_sound_via_sem

/-- info: 'RubyCore.Proof.Judgment.judge_result_vty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms judge_result_vty

/-- info: 'RubyCore.Proof.Judgment.egIf_result_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egIf_result_int

end Judgment
end Proof
end RubyCore
