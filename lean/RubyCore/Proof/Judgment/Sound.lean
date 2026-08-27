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

/-- Preservation, in `invariant_sound_from`'s shape. -/
theorem consecutionJ (m m' : Machine) (h : InvJ m) (hs : SmallStep m m') :
    InvJ m' := by
  have hok := step_okJ h
  unfold SmallStep at hs
  rw [hs] at hok
  exact hok

/-- Progress: a machine satisfying `InvJ` is never one step from a type error. -/
theorem safetyJ (m : Machine) (h : InvJ m) : ¬ aboutToTypeStick m := by
  intro hbad
  have hok := step_okJ h
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
theorem initiationJ {p : Expr} {F : Decls} {τ : Ty} {Γ' : Env} {D' : Decls}
    (hD : DeclsOkJ F Boot.initHeap)
    (hmf : MFrag p)
    (hj : Judge F [] p true topJCtx τ Γ' D') : InvJ (Machine.init p) := by
  refine ⟨
    (show NoHook (Machine.init p).heap from
      noHookB_sound (by decide : noHookB Boot.initHeap = true)),
    (show Saturated (Machine.init p).heap from
      saturatedB_sound (by decide : saturatedB Boot.initHeap = true)),
    (show LitClsOk (Machine.init p).heap from
      ⟨⟨(by decide : (Boot.initHeap.classPayload? Boot.stringId).isSome = true),
        (by rfl : className Boot.initHeap Boot.stringId = "String")⟩,
       ⟨(by decide : (Boot.initHeap.classPayload? Boot.arrayId).isSome = true),
        (by rfl : className Boot.initHeap Boot.arrayId = "Array")⟩⟩),
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
      fun _ => rfl, trivial⟩
    · show (Boot.initHeap.classPayload? Boot.objectId).isSome = true
      decide
    · exact fun _ => (show ClassOk (Machine.init p).heap from
        classOkB_sound (by decide : classOkB Boot.initHeap = true)).1
    · exact fun hz => absurd rfl hz
    · exact fun sc hsc => absurd hsc (by simp [topJCtx, jctxs])
    · simp [Machine.init, Machine.initOn, Array.getD]
  · refine ⟨fun x pr σ _ hf _ => absurd hf (by simp [Machine.init, Machine.initOn]), ?_⟩
    show CtlOkJ F topJCtx [] [] (Machine.init p)
    exact ⟨hmf, τ, τ, Γ', D', Γ', hj, SubJ.refl τ, SubEnv.refl Γ',
      KontOkJ.nil (by simp [topJCtx]) (by simp [topJCtx])⟩

/-- **The composed theorem** — a derivation is a type-safety certificate. Note
    what the statement does not mention: `infer`, `chk`, or any checker at all;
    the J2 `Deriv.check` rung supplies `hj` from a serialized certificate. -/
theorem judge_sound {p : Expr} {F : Decls} {τ : Ty} {Γ' : Env} {D' : Decls}
    (hD : DeclsOkJ F Boot.initHeap)
    (hmf : MFrag p)
    (hj : Judge F [] p true topJCtx τ Γ' D') :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  invariant_sound_from InvJ (initiationJ hD hmf hj) consecutionJ safetyJ

/-! ## The boot table's J-witness

`tableOk_declsOk`'s conclusion converted at its own witnesses: every `baseDecls`
row is discharged by the **builtin** arm, which `EntryOk` and `EntryOkJ` share, so
the conversion never meets the user arm. Stated as a lemma about the old
conclusion rather than a re-derivation, because the old proof's per-row content
(the `entryOk_int` witnesses) is arm-specific already. -/

theorem tableOk_declsOkJ {h : Heap} (ht : TableOk h) (hcls : ClassOk h) :
    DeclsOkJ baseDecls h := by
  have hd := tableOk_declsOk ht hcls
  refine ⟨?_, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩
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
theorem declsOkJ_declsOf {p : Expr} : DeclsOkJ (declsOf p) Boot.initHeap := by
  show DeclsOkJ baseDecls Boot.initHeap
  exact tableOk_declsOkJ tableOk_initHeap classOk_initHeap

/-! ## The first end-to-end instance

`x = 1; if true then x else 0 end` — `StaticSoundness.lean`'s `egIf`, certified by
a hand-built derivation instead of a checker run. -/

/-- The derivation: sequence of an assignment and a branch, every leaf a literal
    rule, the join at `.int` by `SubJ.refl`. -/
theorem egIf_judged : Judge (declsOf Static.egIf) [] Static.egIf true topJCtx
    .int [("x", .int)] (declsOf Static.egIf) := by
  refine .seq (.cons (.vasgnLvar (by rfl) .int) (.single (.ifElse .tru ?_ (.int)
    (SubJ.refl _) (SubJ.refl _) (SubEnv.refl _) (SubEnv.refl _))))
  exact .varLvar (by decide)

theorem egIf_mfrag : MFrag Static.egIf :=
  mfragB_sound (n := 8) (by decide)

/-- **The theorem `check_sound` proves for `egIf`, re-derived through the judgment
    layer** — same conclusion, no checker in the derivation chain. -/
theorem egIf_judge_safe :
    ∀ r, ReachableResult (Machine.init Static.egIf) r → ¬ typeStuck r :=
  judge_sound declsOkJ_declsOf egIf_mfrag egIf_judged

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.Proof.Judgment.judge_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms judge_sound

/-- info: 'RubyCore.Proof.Judgment.egIf_judge_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egIf_judge_safe

end Judgment
end Proof
end RubyCore
