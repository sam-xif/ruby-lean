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
theorem consecution (m m' : Machine) (h : Inv m) (hs : SmallStep m m') :
    Inv m' := by
  have hok := step_ok h
  unfold SmallStep at hs
  rw [hs] at hok
  exact hok

/-- Progress: a machine satisfying `Inv` is never one step from a type error.
    Every `StepResult` other than `.next`/`.done` is `False` under `StepOk`, so
    `.uncaught` in particular is unreachable. -/
theorem safety (m : Machine) (h : Inv m) : ¬ aboutToTypeStick m := by
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
   ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   -- L152's nullary row resolves by the same eight `rfl`s: `IntBuiltinResolves` is a
   -- fact about the method table, and a table entry does not know its own arity.
   ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Initiation, for the machine `Machine.init` builds. -/
theorem initiation {p : Expr} (h : check p = .accept) : Inv (Machine.init p) := by
  -- `DeclsOk` is what the invariant carries now (F1a), and `tableOk_declsOk` is
  -- how the boot heap's three concrete `rfl`-proved resolutions become it.
  refine ⟨
    -- L153: the clause is now a bounded `∀` over class objects, so it is `noHookB`
    -- at a literal heap rather than one `rfl` — the same shape `Saturated` has.
    (show NoHook (Machine.init p).heap from
      noHookB_sound (by decide : noHookB Boot.initHeap = true)),
    -- L148's third heap conjunct. The boot heap is a literal, so the walk's
    -- saturation is decidable *in the kernel* — no certificate needed here, unlike
    -- at the prelude-booted heap where `Lean.Json.parse` does not reduce (L135).
    (show Saturated (Machine.init p).heap from
      saturatedB_sound (by decide : saturatedB Boot.initHeap = true)),
    -- L151's fourth heap conjunct, the producer's. `Boot.stringId` is a literal in a
    -- literal heap, so both halves are kernel computations — the same reason
    -- `Saturated` needs no certificate here and does at the prelude-booted heap.
    (show StrClsOk (Machine.init p).heap from
      ⟨(by decide : (Boot.initHeap.classPayload? Boot.stringId).isSome = true),
       (by rfl : className Boot.initHeap Boot.stringId = "String")⟩),
    -- L156's fifth heap conjunct: `Object`'s constant table binds every reopenable
    -- class name to a non-module class. A literal heap, so `decide` — and the reason
    -- `reopenableClasses` is a table is that this is what a row costs.
    (show ClassOk (Machine.init p).heap from
      classOkB_sound (by decide : classOkB Boot.initHeap = true)),
    -- L155's sixth conjunct, and the only one that is not about the heap: the
    -- outermost activation's definee is `Object`. `Machine.init` builds exactly
    -- one frame and it is the toplevel one, so this is a computation on a literal.
    (show BottomObj (Machine.init p).frames (Machine.init p).stack by
      simp [Machine.init, Machine.initOn, BottomObj]),
    -- **The table the run starts at is `declsOf p`** (F1b.8). It is existential in
    -- `Inv` because it changes along the run; this is where it is pinned, and the
    -- `DeclsOk` obligation is the one F1a already discharged.
    declsOf p, "Object", [], [], tableOk_declsOk tableOk_initHeap, ?_, ?_, ?_⟩
  · show FramesOk (Machine.init p).heap (Machine.init p).frames
      (Machine.init p).stack ([] :: [])
    -- L154 leaves one goal `simp` cannot close: the toplevel frame's definee is
    -- `Object`, and the clause is now that it is a *class* rather than that it is
    -- that id — one `decide` at a literal heap.
    simp [Machine.init, Machine.initOn, FramesOk, FrameConforms, envGet?]
    decide
  · -- **The toplevel activation's context is `Object`** (F1b.9), which is
    -- `BottomObj` again, one level more informative: the bottom frame's definee is
    -- the `Object` id, and the boot heap names that id `"Object"`. Both are
    -- computations on a literal heap. `defVis` is the frame literal's default —
    -- and note that a *toplevel* `def` is nevertheless private
    -- (`Interp.lean:225`), which is why no row can come from one.
    show StackCtx (Machine.init p).heap (Machine.init p).frames
      (Machine.init p).stack ("Object" :: [])
    refine ⟨?_, ?_, ?_, trivial⟩
    · show (Boot.initHeap.classPayload? Boot.objectId).isSome = true
      decide
    · exact (show ClassOk (Machine.init p).heap from
        classOkB_sound (by decide : classOkB Boot.initHeap = true)).1
    -- Vacuous at the outermost frame, and that is the point: a toplevel `def`
    -- installs a **private** method, so no row can come from one (F1b.9/F1b.10).
    · exact fun hz => absurd rfl hz
  · unfold check at h
    show CtlOk (declsOf p) "Object" [] [] (Machine.init p)
    unfold CtlOk
    split at h
    · rename_i r hr
      obtain ⟨τ, Γ', D'⟩ := r
      exact ⟨τ, Γ', D', hr, KontOk.nil⟩
    · exact absurd h (by split <;> simp)

/-- **Static soundness, from any machine satisfying the invariant.** Stated this
    way so that P1's prelude-booted start (`Prelude.initWithPrelude`, the
    starting configuration `SorbetSafety.lean:100` insists on) is an instance
    rather than a restatement. -/
theorem sound_from {m₀ : Machine} (h : Inv m₀) :
    ∀ r, ReachableResult m₀ r → ¬ typeStuck r :=
  invariant_sound_from Inv h consecution safety

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

/-- **A reopened class carrying a user-defined method** (L156):

        class String
          def shout
            1
          end
        end

    The first program the checker accepts that has a **class body** in it, and
    therefore the first whose accepting run passes through a frame that is not the
    toplevel one. Kept as a checked fact rather than a comment because the corpus
    cannot witness it: `--check` over the 1,227 bootstraptest ASTs is byte-identical
    across L156, since none of those programs reopens a core class. The rung is
    inert *on the corpus* and not inert *in capability*, and that distinction is
    only visible if something in the build asserts the capability. -/
def egClassBody : Expr :=
  .class' "String" none (.def' "shout" [] (.int 1))

example : check egClassBody = .accept := by
  simp [check, egClassBody, infer, declsOf, declaresName, baseDecls, reopenableClasses,
    defFree, defFreeAll, addRow, declsFor]

theorem egClassBody_safe :
    ∀ r, ReachableResult (Machine.init egClassBody) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egClassBody, infer, declsOf, declaresName, baseDecls, reopenableClasses,
      defFree, defFreeAll, addRow, declsFor])

/-- **The first accepted program with a user-method call** (F1b.10):

        class String
          def shout
            1
          end
          "x".shout
        end

    and it type-checks at `Integer` — the return type of the program's *own*
    `def`, read back at the call site through a row the `def` step put in the
    table. Everything F1a through F1b.9 built is on this one path: the row is
    keyed on `"String"` (F1a's table), the receiver's type comes from the string
    literal producer (L151), the call is a zero-argument send (L152) inside a
    reopened class body (L156), the send's dispatch takes `EntryOk`'s **user** arm
    (L157 — inhabited for the first time here), the table is threaded (L160) and
    the body's typing survives the later table (L161), and the row's key is tied to
    the frame's definee by `StackCtx` (L162).

    It is also the first accepted program whose *runtime* passes through
    `enterUserMethod`. CRuby and the model agree on it (`p "x".shout` prints `1`
    in both), which is not something `check_sound` says and is worth having said. -/
def egUserCall : Expr :=
  .class' "String" none
    (.seq [ .def' "shout" [] (.int 1),
            .send (some (.str "x")) "shout" [] none ])

example : check egUserCall = .accept := by
  simp [check, egUserCall, infer, inferSeq, declsOf, declaresName, baseDecls,
    reopenableClasses, defFree, defFreeAll, addRow, declsFor, sigOf, declFor,
    declOf?, tyClassNames, groundClassNames]

theorem egUserCall_safe :
    ∀ r, ReachableResult (Machine.init egUserCall) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egUserCall, infer, inferSeq, declsOf, declaresName, baseDecls,
      reopenableClasses, defFree, defFreeAll, addRow, declsFor, sigOf, declFor,
      declOf?, tyClassNames, groundClassNames])

/-- **A toplevel `def` declares nothing, and the call is `unknown`** — which is
    not a limitation of the rule but of Ruby: `Interp.lean:225` makes a toplevel
    method **private**, and `ResolvesUser` requires `.pub`, so a row keyed there
    would be unwitnessable. Kept as a checked fact because it is the constraint
    that decided the rung's shape (F1b.9). -/
example : check (.seq [ .def' "shout" [] (.int 1), .vcall "shout" ]) = .unknown := by
  simp [check, infer, inferSeq, illTyped, illTypedAny, declsOf, declaresName,
    baseDecls, defFree, defFreeAll]

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

/-- **The first accepted program that allocates** (L151), and therefore the first
    whose safety theorem is about a heap the program itself grew. `s = "hi"; s` was
    `unknown` at F0, F1a and F1b.1 — not because anything refuted it, but because
    `infer` had no rule for a string literal and `Ty` had no inhabitant that was an
    object.

    Read the type: `s` is bound at `.cls "String"`, so the accept genuinely goes
    through the class arm of `Ty`, the `.ref` arm of `valueTy?` and the class arm of
    `declFor` — the three pieces F1b.1 added with nothing to exercise them. -/
def egStr : Expr :=
  .seq [ .vasgn .lvar "s" (.str "hi"), .var .lvar "s" ]

example : check egStr = .accept := by
  simp [check, egStr, infer, inferSeq, envSet, envGet?, declsOf]

theorem egStr_safe : ∀ r, ReachableResult (Machine.init egStr) r → ¬ typeStuck r :=
  check_sound (by simp [check, egStr, infer, inferSeq, envSet, envGet?, declsOf])

/-- The same, mixed with the arithmetic fragment: an allocation happens *between*
    two typed integer sends, so `KontOk`'s stored `ValueTy` facts really are
    transported across a growing heap rather than across a `rfl`. That transport is
    L143–L149's whole arc, and this is the first program that runs it. -/
def egStrSeq : Expr :=
  .seq [ .vasgn .lvar "n" (.send (some (.int 1)) "+" [.int 2] none),
         .vasgn .lvar "s" (.str "hi"),
         .send (some (.var .lvar "n")) "*" [.int 4] none ]

theorem egStrSeq_safe :
    ∀ r, ReachableResult (Machine.init egStrSeq) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egStrSeq, infer, inferSeq, declsOf, sigOf, declFor, declOf?,
      declsFor, baseDecls, tyClassNames, envSet, envGet?])

/-- **The first zero-argument send** (L152). `(1 + 2).zero?` is typed end to end:
    the inner send through `recvK`/`argsK` as before, the outer through the new
    `recvK0`, which dispatches in the `recvK` step itself because `startArgs … [] []`
    is `finishSend`. The result is `.bool`, so this is also the first accepted program
    whose type comes from a declaration with a return type unlike its receiver's. -/
def egZero : Expr :=
  .send (some (.send (some (.int 1)) "+" [.int 2] none)) "zero?" [] none

theorem egZero_safe : ∀ r, ReachableResult (Machine.init egZero) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egZero, infer, declsOf, sigOf, declFor, declOf?, declsFor,
      baseDecls, tyClassNames])

/-- Arity is carried by the *declaration*, not by the builtin: `Integer#zero?`
    ignores its arguments entirely, and it is `baseDecls`'s `params := []` plus
    `infer`'s zero-argument arm that make this `unknown` rather than typed. -/
example : check (.send (some (.int 1)) "zero?" [.int 5] none) = .unknown := by
  simp [check, infer, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?,
    declsFor, baseDecls, tyClassNames, declsOf]

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
