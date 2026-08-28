import RubyCore.Proof.Judgment.Preservation
import RubyCore.Proof.StaticSoundness

/-!
# The composed theorem (J21): a `Judge` derivation certifies type safety

`judgment-layer.md` J1's exit: `InvJ` plugged into the already-proved
`invariant_sound_from`. The three obligations are `step_okJ` read twice
(consecution and safety) and `initiationJ` — the boot-heap facts of
`initiation_ctl` (Proof/StaticSoundness.lean:102) with the control clause
discharged from a derivation instead of an `infer` run.

`judge_sound` is the headline: a `MFrag` program with a root derivation at a table
sound for the boot heap has no reachable type-stuck outcome. The J2 rung
(`Deriv.check`) supplies the derivation from a checked certificate; the worked
example at the bottom supplies one by hand, which makes this file the first
end-to-end instance of the pivot — machine-checked safety with **no checker
function in the statement at all**.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

set_option maxRecDepth 100000

/-- Preservation, in `invariant_sound_from`'s shape — at every answer type (J29),
    conditional on the semantic axioms' obligations (J31). -/
theorem consecutionJ {ans : Ty} {A : SemAxioms} (hax : SemAxiomsOk A)
    (m m' : Machine) (h : InvJ ans A m) (hs : SmallStep m m') :
    InvJ ans A m' := by
  have hok := step_okJ hax h
  unfold SmallStep at hs
  rw [hs] at hok
  exact hok

/-- Progress: a machine satisfying `InvJ` is never one step from a type error. -/
theorem safetyJ {ans : Ty} {A : SemAxioms} (hax : SemAxiomsOk A)
    (m : Machine) (h : InvJ ans A m) : ¬ aboutToTypeStick m := by
  intro hbad
  have hok := step_okJ hax h
  unfold aboutToTypeStick typeStuck at hbad
  cases hr : stepFn m with
  | next m' => rw [hr] at hbad; exact hbad
  | done v m' => rw [hr] at hbad; exact hbad
  | uncaught exc m' => rw [hr] at hok hbad; exact hok hbad
  | unsupported r => rw [hr] at hbad; exact hbad
  | stuck msg => rw [hr] at hbad; exact hbad

/-- The toplevel context, as the judgment sees it. -/
def topJCtx : JCtx := { cls := "Object" }

/-- **Initiation**: the boot facts of `initiation_ctl`, with the control clause
    from a derivation. The heap-side proofs are the old ones verbatim — they are
    computations on a literal heap and mention no typing layer. -/
theorem initiationJ {A : SemAxioms} {p : Expr} {F : Decls} {τ : Ty} {Γ' : Env}
    {D' : Decls}
    (hD : DeclsOkJ A F Boot.initHeap)
    (hmf : MFrag A p)
    (hfr : fragHead p = true)
    (hj : Judge A F [] p true topJCtx τ Γ' D') : InvJ τ A (Machine.init p) := by
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
    (by simp [Machine.init, Machine.initOn, framePopLabels]),
    (by intro κ hm; simp [Machine.init, Machine.initOn] at hm),
    F, topJCtx, [], [],
    hD, ?_, ?_, ?_⟩
  · show FramesOkJ (Machine.init p).heap (Machine.init p).frames
      (Machine.init p).stack ([] :: [])
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
  · refine ⟨fun x pr σ _ hf _ => absurd hf (by simp [Machine.init, Machine.initOn]), ?_⟩
    show CtlOkJ F topJCtx [] [] τ A (Machine.init p)
    exact Or.inl ⟨hfr, hmf, τ, τ, Γ', D', Γ', hj, SubJ.refl τ, SubEnv.refl Γ',
      KontOkJ.nil (SubJ.refl τ) (by simp [topJCtx]) (by simp [topJCtx])⟩

/-- **The composed theorem** — a derivation is a type-safety certificate. Note
    what the statement does not mention: `infer`, `chk`, or any checker at all;
    the J2 `Deriv.check` rung supplies `hj` from a serialized certificate. -/
theorem judge_sound {A : SemAxioms} {p : Expr} {F : Decls} {τ : Ty} {Γ' : Env}
    {D' : Decls}
    (hax : SemAxiomsOk A)
    (hD : DeclsOkJ A F Boot.initHeap)
    (hmf : MFrag A p)
    (hfr : fragHead p = true)
    (hj : Judge A F [] p true topJCtx τ Γ' D') :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  invariant_sound_from (InvJ τ A) (initiationJ hD hmf hfr hj)
    (consecutionJ hax) (safetyJ hax)

/-! ## The boot table's J-witness

`tableOk_declsOk`'s conclusion converted at its own witnesses: every `baseDecls`
row is discharged by the **builtin** arm, which `EntryOk` and `EntryOkJ` share, so
the conversion never meets the user arm. Stated as a lemma about the old
conclusion rather than a re-derivation, because the old proof's per-row content
(the `entryOk_int` witnesses) is arm-specific already. -/

/-- Every `baseDecls` row's parameters are ground — by walking the literal. -/
theorem declFor_baseDecls_ground {τr : Ty} {mname : String} {d : MethodDecl}
    (h : declFor baseDecls τr mname = some d) :
    ∀ p ∈ d.params, groundTy p = true := by
  have hshape : d.params = [Ty.int] ∨ d.params = [] := by
    unfold declFor at h
    cases htn : tyClassNames τr with
    | nil => rw [htn] at h; exact absurd h (by simp)
    | cons c cs =>
      rw [htn] at h
      cases hdo : declOf? baseDecls c mname with
      | none => simp only [hdo] at h; exact absurd h (by simp)
      | some d0 =>
        simp only [hdo] at h
        have hd0 : d0 = d := by
          by_cases hall : cs.all (fun c' => declOf? baseDecls c' mname == some d0) = true
          · simp only [hall, if_true, Option.some.injEq] at h
            exact h
          · simp only [hall, Bool.false_eq_true, if_false] at h
            exact absurd h (by simp)
        subst hd0
        unfold declOf? at hdo
        simp only [Option.map_eq_some_iff] at hdo
        obtain ⟨e, he, hed⟩ := hdo
        have hmem := List.mem_of_find?_eq_some he
        unfold declsFor at hmem
        cases hf : baseDecls.rows.find? (·.1 == c) with
        | none => rw [hf] at hmem; simp at hmem
        | some pr =>
          rw [hf] at hmem
          have hpr := List.mem_of_find?_eq_some hf
          have hpr' : pr = ("Integer",
              [("+", { params := [Ty.int], ret := Ty.int }),
               ("-", { params := [Ty.int], ret := Ty.int }),
               ("*", { params := [Ty.int], ret := Ty.int }),
               ("zero?", { params := [], ret := Ty.bool })]) := by
            simpa [baseDecls] using hpr
          rw [hpr'] at hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl | rfl | rfl <;> (rw [← hed]; simp)
  rcases hshape with hp | hp <;> rw [hp] <;> intro p hpm
  · simp only [List.mem_singleton] at hpm
    subst hpm
    rfl
  · simp at hpm

theorem tableOk_declsOkJ {A : SemAxioms} {h : Heap} (ht : TableOk h) (hcls : ClassOk h) :
    DeclsOkJ A baseDecls h := by
  have hd := tableOk_declsOk ht hcls
  refine ⟨?_, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2,
    fun τr mname d hdecl => declFor_baseDecls_ground hdecl,
    fun c x τ hn => absurd hn (by simp [ivarTy?, baseDecls]),
    fun x τ hn => absurd hn (by simp [globalTy?, baseDecls]),
    fun pr hpr => absurd hpr (by simp [baseDecls])⟩
  intro τr mname d hdecl
  rcases hd.1 τr mname d hdecl with hb | ⟨mdu, cu, htys, hres, hnm, hconf⟩ | hi
  · exact Or.inl hb
  · -- No `baseDecls` row resolves to a user method at any heap `TableOk` describes:
    -- refute from the table's shape — the only declared receivers are `Integer`s,
    -- whose rows `tableOk_declsOk` witnesses by builtins. The user arm cannot be
    -- ruled out *here* without re-walking the table, so walk it: only `.int` rows
    -- exist, and `UserKey (.int) c` is false.
    rcases htys with heq | ⟨⟨e, he⟩, hcu⟩
    · -- `τr = .cls cu`: `baseDecls` keys only `Integer`, which is ground, so the
      -- class arm's lookup misses either way.
      subst heq
      by_cases hg : cu ∈ groundClassNames
      · exact absurd hdecl (by simp [declFor, tyClassNames, hg])
      · have hne : ("Integer" == cu) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro hq
          exact hg (hq ▸ (by decide))
        exact absurd hdecl
          (by simp [declFor, tyClassNames, hg, declOf?, declsFor, baseDecls, hne])
    · subst he
      exact absurd hdecl (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
  · exact Or.inr (Or.inr hi)

/-- `declsOf` is constant at `baseDecls` today; the J-witness at the boot heap, in
    the shape `judge_sound` consumes. -/
theorem declsOkJ_declsOf {A : SemAxioms} {p : Expr} :
    DeclsOkJ A (declsOf p) Boot.initHeap := by
  show DeclsOkJ A baseDecls Boot.initHeap
  exact tableOk_declsOkJ tableOk_initHeap classOk_initHeap

/-! ## The first end-to-end instance

`x = 1; if true then x else 0 end` — `StaticSoundness.lean`'s `egIf`, certified by
a hand-built derivation instead of a checker run. -/

/-- The derivation: sequence of an assignment and a branch, every leaf a literal
    rule, the join at `.int` by `SubJ.refl`. -/
theorem egIf_judged : Judge [] (declsOf Static.egIf) [] Static.egIf true topJCtx
    .int [("x", .int)] (declsOf Static.egIf) := by
  refine .seq (.cons (.vasgnLvar (by rfl) .int) (.single (.ifElse .tru ?_ (.int)
    (SubJ.refl _) (SubJ.refl _) (SubEnv.refl _) (SubEnv.refl _))))
  exact .varLvar (by decide)

theorem egIf_mfrag : MFrag [] Static.egIf :=
  mfragB_sound (A := []) (n := 8) (by decide)

/-- **The theorem `check_sound` proves for `egIf`, re-derived through the judgment
    layer** — same conclusion, no checker in the derivation chain. -/
theorem egIf_judge_safe :
    ∀ r, ReachableResult (Machine.init Static.egIf) r → ¬ typeStuck r :=
  judge_sound semAxiomsOk_nil declsOkJ_declsOf egIf_mfrag (by decide) egIf_judged

/-- **The first send certified through the judgment layer**: `(1 + 2).zero?`
    (`StaticSoundness.lean`'s `egZero`), its derivation reading two `baseDecls`
    rows — a builtin dispatch end to end. -/
theorem egZero_judged : Judge [] (declsOf Static.egZero) [] Static.egZero true topJCtx
    .bool [] (declsOf Static.egZero) := by
  have hplus : sigOf (declsOf Static.egZero) .int "+" = some ([.int], .int) := by decide
  have hzero : sigOf (declsOf Static.egZero) .int "zero?" = some ([], .bool) := by decide
  exact .send (.expl (.send (.expl .int) (.cons .int .nil) hplus
    (.cons (SubJ.refl _) .nil))) .nil hzero .nil

theorem egZero_mfrag : MFrag [] Static.egZero :=
  mfragB_sound (A := []) (n := 8) (by decide)

theorem egZero_judge_safe :
    ∀ r, ReachableResult (Machine.init Static.egZero) r → ¬ typeStuck r :=
  judge_sound semAxiomsOk_nil declsOkJ_declsOf egZero_mfrag (by decide) egZero_judged

/-- **A user-defined method, installed and called, certified through the judgment
    layer** — `egUserCall` (`class String; def shout; 1; end; "x".shout; end`), the
    F1b.10 flagship: the `def` step's row is threaded by `Judge.defPromote` and the
    send reads it back. This is the T5 (`class_hierarchy`) shape end to end. -/
theorem egUserCall_judged : Judge [] (declsOf Static.egUserCall) [] Static.egUserCall
    true topJCtx .int []
    (addRow (declsOf Static.egUserCall) "String" "shout"
      { params := [], ret := .int }) := by
  have hsig : sigOf (addRow (declsOf Static.egUserCall) "String" "shout"
        { params := [], ret := .int }) (.cls "String") "shout"
      = some ([], .int) := by decide
  have hdef : Judge [] (declsOf Static.egUserCall) [] (.def' "shout" [] (.int 1)) false
      ({ cls := "String", inClassBody := true } : JCtx) .sym []
      (addRow (declsOf Static.egUserCall) "String" "shout"
        { params := [], ret := .int }) :=
    .defPromote (by decide) (by decide) .int rfl (by decide) (by decide)
      (by decide) (by simp [defFree]) rfl rfl rfl
  have hsend : Judge [] (addRow (declsOf Static.egUserCall) "String" "shout"
        { params := [], ret := .int }) []
      (.send (some (.str "x")) "shout" [] none) false ({ cls := "String", inClassBody := true } : JCtx)
      .int []
      (addRow (declsOf Static.egUserCall) "String" "shout"
        { params := [], ret := .int }) :=
    .send (.expl .str) .nil hsig .nil
  exact .classTop (by decide) (.seq (.cons hdef (.single hsend)))

theorem egUserCall_mfrag : MFrag [] Static.egUserCall :=
  mfragB_sound (A := []) (n := 12) (by decide)

theorem egUserCall_judge_safe :
    ∀ r, ReachableResult (Machine.init Static.egUserCall) r → ¬ typeStuck r :=
  judge_sound semAxiomsOk_nil declsOkJ_declsOf egUserCall_mfrag (by decide) egUserCall_judged

/-- **The receiverless user-method call** — `egVcall`, fourteen of the slice's
    ninety-two method bodies' shape (F1b.11), through two threaded rows. -/
theorem egVcall_judged : Judge [] (declsOf Static.egVcall) [] Static.egVcall
    true topJCtx .int []
    (addRow (addRow (declsOf Static.egVcall) "String" "value"
        { params := [], ret := .int }) "String" "get"
      { params := [], ret := .int }) := by
  have hsigv : sigOf (addRow (declsOf Static.egVcall) "String" "value"
        { params := [], ret := .int }) (.cls "String") "value"
      = some ([], .int) := by decide
  have hsigg : sigOf (addRow (addRow (declsOf Static.egVcall) "String" "value"
          { params := [], ret := .int }) "String" "get"
        { params := [], ret := .int }) (.cls "String") "get"
      = some ([], .int) := by decide
  have hdefv : Judge [] (declsOf Static.egVcall) [] (.def' "value" [] (.int 1)) false
      ({ cls := "String", inClassBody := true } : JCtx) .sym []
      (addRow (declsOf Static.egVcall) "String" "value"
        { params := [], ret := .int }) :=
    .defPromote (by decide) (by decide) .int rfl (by decide) (by decide)
      (by decide) (by simp [defFree]) rfl rfl rfl
  have hdefg : Judge [] (addRow (declsOf Static.egVcall) "String" "value"
        { params := [], ret := .int }) []
      (.def' "get" [] (.vcall "value")) false ({ cls := "String", inClassBody := true } : JCtx) .sym []
      (addRow (addRow (declsOf Static.egVcall) "String" "value"
          { params := [], ret := .int }) "String" "get"
        { params := [], ret := .int }) :=
    .defPromote (by decide) (by decide) (.vcall rfl hsigv) rfl (by decide)
      (by decide) (by decide) (by simp [defFree]) rfl rfl rfl
  have hsend : Judge [] (addRow (addRow (declsOf Static.egVcall) "String" "value"
          { params := [], ret := .int }) "String" "get"
        { params := [], ret := .int }) []
      (.send (some (.str "x")) "get" [] none) false ({ cls := "String", inClassBody := true } : JCtx)
      .int []
      (addRow (addRow (declsOf Static.egVcall) "String" "value"
          { params := [], ret := .int }) "String" "get"
        { params := [], ret := .int }) :=
    .send (.expl .str) .nil hsigg .nil
  exact .classTop (by decide) (.seq (.cons hdefv (.cons hdefg (.single hsend))))

theorem egVcall_mfrag : MFrag [] Static.egVcall :=
  mfragB_sound (A := []) (n := 12) (by decide)

theorem egVcall_judge_safe :
    ∀ r, ReachableResult (Machine.init Static.egVcall) r → ¬ typeStuck r :=
  judge_sound semAxiomsOk_nil declsOkJ_declsOf egVcall_mfrag (by decide) egVcall_judged

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.Proof.Judgment.judge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms judge_sound

/-- info: 'RubyCore.Proof.Judgment.egIf_judge_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egIf_judge_safe

/-- info: 'RubyCore.Proof.Judgment.egZero_judge_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egZero_judge_safe

/-- info: 'RubyCore.Proof.Judgment.egUserCall_judge_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egUserCall_judge_safe

/-- info: 'RubyCore.Proof.Judgment.egVcall_judge_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egVcall_judge_safe

end Judgment
end Proof
end RubyCore
