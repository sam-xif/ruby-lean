import RubyCore.Proof.Static.Preservation

/-!
# P0 — static soundness on the fully-typed fragment

`docs/semantics/static-soundness-poc.md`. The claim:

    check P = .accept  →  no reachable outcome is `typeStuck`

proved by handing `Proof.invariant_sound_from` an invariant built from the
checker of `Types/Core.lean`. Nothing here re-derives reachability: the
metatheorem harness (`Proof/TypeSafety.lean:157`) is bad-state-agnostic and
already proved, and this is the first target to reuse `typeStuck`
*unmodified* — no bad-state swap at all.

Note the conclusion is `typeStuck`, not `sorbetStuck`: in a fully-typed
fragment a sig check cannot fire, so the blame carve-out of
`Proof/SorbetSafety.lean` is unnecessary and the *strong* property is what
gets proved (doc §2.1).

## Shape of the invariant

    Inv m  ≡  TableOk m.heap ∧ NoHook m.heap ∧
                ∃ Γ Γs, FramesOk m.frames m.stack (Γ :: Γs) ∧ CtlOk Γ Γs m

`CtlOk`/`KontOk` play the role the doc §4 assigns to `InFragment`: they simply
have **no constructor** for the machine shapes outside the fragment, so the
`stepFn` case analysis discharges those branches by contradiction rather than
by typing work. That is the whole tractability argument, and it is why this
file does not need a separate fragment predicate.

**Split, L136.** §1 is `Proof/Static/Locals.lean`, §2 `Proof/Static/Konts.lean`,
§3 `Proof/Static/Preservation.lean`; what remains here is the theorem itself, its
worked examples and the axiom audit. The file kept its name because
`check_sound` is what everything downstream imports.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

set_option maxRecDepth 100000

/-! ## 4. The three obligations, and the theorem -/

/-- Preservation. -/
theorem consecution (D : Decls) (m m' : Machine) (h : Inv D m) (hs : SmallStep m m') :
    Inv D m' := by
  have hok := step_ok h
  unfold SmallStep at hs
  rw [hs] at hok
  exact hok

/-- Progress: a machine satisfying `Inv` is never one step from a type error.
    Every `StepResult` other than `.next`/`.done` is `False` under `StepOk`, so
    `.uncaught` in particular is unreachable. -/
theorem safety (D : Decls) (m : Machine) (h : Inv D m) : ¬ aboutToTypeStick m := by
  intro hbad
  have hok := step_ok h
  unfold aboutToTypeStick typeStuck at hbad
  cases hr : stepFn m with
  | next m' => rw [hr] at hbad; exact hbad
  | done v m' => rw [hr] at hbad; exact hbad
  | uncaught exc m' => rw [hr] at hok; exact hok
  | unsupported r => rw [hr] at hbad; exact hbad
  | stuck msg => rw [hr] at hbad; exact hbad

/-- The boot heap satisfies the table condition — **by `rfl`**, which is what
    keeps `check_sound` unconditional. Were this only reachable by
    `native_decide` the headline theorem would inherit `ofReduceBool`; L73's
    reducibility discipline is what makes it come out this way. -/
theorem tableOk_initHeap : TableOk Boot.initHeap :=
  ⟨⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Initiation, for the machine `Machine.init` builds. -/
theorem initiation {p : Expr} (h : check p = .accept) : Inv (declsOf p) (Machine.init p) := by
  -- `DeclsOk` is what the invariant carries now (F1a), and `tableOk_declsOk` is
  -- how the boot heap's three concrete `rfl`-proved resolutions become it.
  refine ⟨tableOk_declsOk tableOk_initHeap,
    (by rfl : NoHook (Machine.init p).heap), [], [], ?_, ?_⟩
  · show FramesOk (Machine.init p).heap (Machine.init p).frames
      (Machine.init p).stack ([] :: [])
    simp [Machine.init, Machine.initOn, FramesOk, FrameConforms, envGet?]
  · unfold check at h
    show CtlOk (declsOf p) [] [] (Machine.init p)
    unfold CtlOk
    split at h
    · rename_i r hr
      obtain ⟨τ, Γ'⟩ := r
      exact ⟨τ, Γ', hr, KontOk.nil⟩
    · exact absurd h (by split <;> simp)

/-- **Static soundness, from any machine satisfying the invariant.** Stated this
    way so that P1's prelude-booted start (`Prelude.initWithPrelude`, the
    starting configuration `SorbetSafety.lean:100` insists on) is an instance
    rather than a restatement. -/
theorem sound_from {D : Decls} {m₀ : Machine} (h : Inv D m₀) :
    ∀ r, ReachableResult m₀ r → ¬ typeStuck r :=
  invariant_sound_from (Inv D) h (consecution D) (safety D)

/-- **The POC theorem.** `check` accepts ⇒ no reachable outcome is a type
    error. Unconditional: no rely condition, no assumed hypothesis. -/
theorem check_sound {p : Expr} (h : check p = .accept) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  sound_from (initiation h)

/-! ## 5. Worked examples

`decide` runs the checker; the theorem then applies to the program. -/

/-- `x = 1; if true then x else 0 end` -/
def egIf : Expr :=
  .seq [ .vasgn .lvar "x" (.int 1),
         .if' .tru (.var .lvar "x") (some (.int 0)) ]

example : check egIf = .accept := by
  simp [check, egIf, infer, inferSeq, inferIf, envSet, envGet?, declsOf]

theorem egIf_safe : ∀ r, ReachableResult (Machine.init egIf) r → ¬ typeStuck r :=
  check_sound (by simp [check, egIf, infer, inferSeq, inferIf, envSet, envGet?, declsOf])

/-- `x = 0; while true do x = 1 end` — diverges, which safety permits: the
    property is *never type-stuck*, not *terminates*. -/
def egLoop : Expr :=
  .seq [ .vasgn .lvar "x" (.int 0),
         .while' .tru (.vasgn .lvar "x" (.int 1)) ]

example : check egLoop = .accept := by
  simp [check, egLoop, infer, inferSeq, envSet, declsOf]

theorem egLoop_safe : ∀ r, ReachableResult (Machine.init egLoop) r → ¬ typeStuck r :=
  check_sound (by simp [check, egLoop, infer, inferSeq, envSet, declsOf])

/-- `def f; 1 + 2; end; 3 * 4` — the P1b shape. The `def` installs a method,
    mutating the method table (which `TableOk_defineMethod` is what survives), and
    evaluates to `:f`, which the `seq` discards. -/
def egDef : Expr :=
  .seq [ .def' "f" [] (.send (some (.int 1)) "+" [.int 2] none),
         .send (some (.int 3)) "*" [.int 4] none ]

example : check egDef = .accept := by
  simp [check, egDef, infer, inferSeq, declsOf, declaresName, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames]

theorem egDef_safe : ∀ r, ReachableResult (Machine.init egDef) r → ¬ typeStuck r :=
  check_sound (by simp [check, egDef, infer, inferSeq, declsOf, declaresName, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames])

/-- `(x + 1) * 2` with `x` a local — the P0b program shape. -/
def egArith : Expr :=
  .seq [ .vasgn .lvar "x" (.int 3),
         .send (some (.send (some (.var .lvar "x")) "+" [.int 1] none))
               "*" [.int 2] none ]

example : check egArith = .accept := by
  simp [check, egArith, infer, inferSeq, declsOf, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, envSet, envGet?]

theorem egArith_safe :
    ∀ r, ReachableResult (Machine.init egArith) r → ¬ typeStuck r :=
  check_sound (by simp [check, egArith, infer, inferSeq, declsOf, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, envSet, envGet?])

/-- A branch-type disagreement the fragment cannot join: `unknown`, not
    `reject`. `illTyped` has no opinion about `if` arms — it only refutes calls
    the builtin table refutes — so the absence of a union type shows up as
    incompleteness rather than as a claim about the program.

    The verdict examples that *do* exercise `reject` live next to the checker
    in `Types/Core.lean`; only the safety-bearing ones belong here. -/
example : check (.if' .tru (.int 1) (some .nil)) = .unknown := by
  simp [check, infer, inferIf, illTyped, declsOf]

/-! ## 6. Axiom hygiene

The P0 exit criterion. Only the three standard Lean axioms — no `sorry`, and in
particular no `native_decide`/`ofReduceBool`, which is why §5's examples are
discharged by `simp` over the equation lemmas rather than by kernel reduction
(`infer` is well-founded-recursive, so `decide` does not reduce it). Same
baseline as `Proof/SorbetSafety.lean` [V]. -/

/-- info: 'RubyCore.Proof.Static.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_sound

end Static
end Proof
end RubyCore
