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
    Every `StepResult` other than `.next`/`.done`/`.uncaught` is `False` under `StepOk`;
    **`.uncaught` is admitted since L216 and carries `¬ isTypeError` directly**, which is
    this theorem's conclusion at that branch rather than a vacuous refutation. -/
theorem safety (m : Machine) (h : Inv m) : ¬ aboutToTypeStick m := by
  intro hbad
  have hok := step_ok h
  unfold aboutToTypeStick typeStuck at hbad
  cases hr : stepFn m with
  | next m' => rw [hr] at hbad; exact hbad
  | done v m' => rw [hr] at hbad; exact hbad
  | uncaught exc m' => rw [hr] at hok hbad; exact hok hbad
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

/-- L195: named, because `tableOk_declsOk` now needs it too — the constant half of
    `DeclsOk baseDecls` is `ClassOk` read out at a `baseConsts` entry. -/
theorem classOk_initHeap : ClassOk Boot.initHeap :=
  classOkB_sound (by decide : classOkB Boot.initHeap = true)

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
    (show LitClsOk (Machine.init p).heap from
      ⟨⟨(by decide : (Boot.initHeap.classPayload? Boot.stringId).isSome = true),
        (by rfl : className Boot.initHeap Boot.stringId = "String")⟩,
       ⟨(by decide : (Boot.initHeap.classPayload? Boot.arrayId).isSome = true),
        (by rfl : className Boot.initHeap Boot.arrayId = "Array")⟩⟩),
    -- L156's fifth heap conjunct: `Object`'s constant table binds every reopenable
    -- class name to a non-module class. A literal heap, so `decide` — and the reason
    -- `reopenableClasses` is a table is that this is what a row costs.
    (show ClassOk (Machine.init p).heap from classOk_initHeap),
    -- L155's sixth conjunct, and the only one that is not about the heap: the
    -- outermost activation's definee is `Object`. `Machine.init` builds exactly
    -- one frame and it is the toplevel one, so this is a computation on a literal.
    (show BottomObj (Machine.init p).frames (Machine.init p).stack by
      simp [Machine.init, Machine.initOn, BottomObj]),
    -- **The table the run starts at is `declsOf p`** (F1b.8). It is existential in
    -- `Inv` because it changes along the run; this is where it is pinned, and the
    -- `DeclsOk` obligation is the one F1a already discharged.
    -- L199: `Machine.init` builds one frame and an empty continuation, so both lists
    -- are trivial — `[] = [0].dropLast`.
    (by simp [Machine.init, Machine.initOn, framePopLabels]),
    -- L247: the initial continuation is empty, so the clause is vacuous.
    (by intro κ hm; simp [Machine.init, Machine.initOn] at hm),
    declsOf p, { cls := "Object" }, [], [],
    tableOk_declsOk tableOk_initHeap classOk_initHeap, ?_, ?_, ?_⟩
  · show FramesOk (Machine.init p).heap (Machine.init p).frames
      (Machine.init p).stack ([] :: [])
    -- L154 leaves one goal `simp` cannot close: the toplevel frame's definee is
    -- `Object`, and the clause is now that it is a *class* rather than that it is
    -- that id — one `decide` at a literal heap.
    simp [Machine.init, Machine.initOn, FramesOk, FrameConforms, ShallowChain, envGet?]
    decide
  · -- **The toplevel activation's context is `Object`** (F1b.9), which is
    -- `BottomObj` again, one level more informative: the bottom frame's definee is
    -- the `Object` id, and the boot heap names that id `"Object"`. Both are
    -- computations on a literal heap. `defVis` is the frame literal's default —
    -- and note that a *toplevel* `def` is nevertheless private
    -- (`Interp.lean:225`), which is why no row can come from one.
    show StackCtx (Machine.init p).heap (Machine.init p).frames
      (Machine.init p).stack ({ cls := "Object" } :: [])
    -- L198: the toplevel context declares no return type, so the sixth clause is the
    -- right disjunct — a `return` at toplevel has no target and the desugarer gates it.
    -- L207: and it names no method, so the seventh is vacuous too.
    refine ⟨?_, ?_, ?_, ?_, ?_, Or.inr rfl, fun mn h => absurd h (by simp), fun _ => rfl, trivial⟩
    · show (Boot.initHeap.classPayload? Boot.objectId).isSome = true
      decide
    · exact fun _ => (show ClassOk (Machine.init p).heap from
        classOkB_sound (by decide : classOkB Boot.initHeap = true)).1
    -- Vacuous at the outermost frame, and that is the point: a toplevel `def`
    -- installs a **private** method, so no row can come from one (F1b.9/F1b.10).
    · exact fun hz => absurd rfl hz
    -- The toplevel activation claims no self type: `self` is `main`, and nothing in
    -- the fragment needs it (F1b.11).
    · exact fun sc hsc => absurd hsc (by simp)
    · simp [Machine.init, Machine.initOn, Array.getD]
  · -- **L228: the globals conjunct at the initial machine**, and it is vacuous — the
    -- initial machine has `globals := []`, so the lookup is `none` and no declared
    -- global claims anything yet. What makes it *stay* vacuous is the write rule's
    -- conformance check, not this.
    refine ⟨fun x pr σ _ hf _ => absurd hf (by simp [Machine.init, Machine.initOn]), ?_⟩
    unfold check at h
    show CtlOk (declsOf p) { cls := "Object" } [] [] (Machine.init p)
    unfold CtlOk
    split at h
    · rename_i r hr
      obtain ⟨τ, Γ', D'⟩ := r
      exact ⟨τ, τ, Γ', D', Γ', hr, by simp, SubEnv.refl _, KontOk.nil (by simp) (by simp)⟩
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
  simp [check, egIf, infer, inferArgs, subTys, subTy, inferSeq, inferElems, inferIf, joinTy, constTy?, baseConsts, envSet, envGet?, declsOf, isSelf]

theorem egIf_safe : ∀ r, ReachableResult (Machine.init egIf) r → ¬ typeStuck r :=
  check_sound (by simp [check, egIf, infer, inferArgs, subTys, subTy, inferSeq, inferElems, inferIf, joinTy, constTy?, baseConsts, envSet, envGet?, declsOf, isSelf])

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
  simp [check, egClassBody, infer, inferArgs, subTys, subTy, declsOf, declaresName, baseDecls, readableClasses, reopenableClasses, groundClassNames,
    defFree, defFreeAll, addRow, declsFor, isSelf]

theorem egClassBody_safe :
    ∀ r, ReachableResult (Machine.init egClassBody) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egClassBody, infer, inferArgs, subTys, subTy, declsOf, declaresName, baseDecls, readableClasses, reopenableClasses, groundClassNames,
      defFree, defFreeAll, addRow, declsFor, isSelf])

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
  simp [check, egUserCall, infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf, declaresName, baseDecls,
    readableClasses, reopenableClasses, defFree, defFreeAll, addRow, declsFor, sigOf, declFor,
    declOf?, tyClassNames, groundClassNames, isSelf]

theorem egUserCall_safe :
    ∀ r, ReachableResult (Machine.init egUserCall) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egUserCall, infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf, declaresName, baseDecls,
      readableClasses, reopenableClasses, defFree, defFreeAll, addRow, declsFor, sigOf, declFor,
      declOf?, tyClassNames, groundClassNames, isSelf])

/-- **A method calling another method of the same class, by implicit self**
    (F1b.11):

        class String
          def value
            1
          end
          def get
            value          # ⇒ Integer
          end
          "x".get
        end

    This is the shape of **fourteen of the slice's ninety-two method bodies** —
    `def hash = value.hash`, `def affected? = state == :affected`, `def to_s =
    to_str` — every one of them a receiverless call to a user-defined accessor,
    which is exactly what a program-supplied row is. It is the reason `vcall` and
    not `const` was the rung after the rows, against a node count of 92 to 868.

    Read what the checker had to know to accept it: that `self` inside `get` is a
    `String` (the `StackCtx` clause), that `String#value` is declared (the row
    L163's `def` step added), and that the row's return type is what `value`
    answers (`UserConforms`, the checker's own verdict on `value`'s body, carried
    inside the invariant). -/
def egVcall : Expr :=
  .class' "String" none
    (.seq [ .def' "value" [] (.int 1),
            .def' "get" [] (.vcall "value"),
            .send (some (.str "x")) "get" [] none ])

theorem egVcall_safe :
    ∀ r, ReachableResult (Machine.init egVcall) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egVcall, infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf, declaresName, baseDecls,
      readableClasses, reopenableClasses, defFree, defFreeAll, addRow, declsFor, sigOf, declFor,
      declOf?, tyClassNames, groundClassNames, isSelf])

/-- **The written receiverless call** (L170) — `v()` where `egVcall` writes `v`.

    ```ruby
    class String
      def value; 1; end
      def get
        value()        # ⇒ Integer
      end
      "x".get
    end
    ```

    A different `Expr` constructor (`.send none "value" [] none`, not `.vcall`),
    a different `SendSite` (`.implicit`, not `.vcall`), the **same** dispatch and
    the same one step: `evalExpr` answers both with `startArgs m self site mname
    [] []`, which is `finishSend`, and `visError?` is `none` for every site but
    `.explicit`. So the rule adds no `KontOk` constructor, and
    `inv_implicit_send0` — L164's `vcall` case quantified over the site — is the
    whole consecution argument for both.

    The slice ranked this **11 of its 112 method bodies**, second only to `const`,
    and the census re-ranked on landing exactly as L168 said it would: `return`
    went 8 → 16 and `send-2-args` 8 → 10, because a census classifies at the
    outermost node. -/
def egImplicitCall : Expr :=
  .class' "String" none
    (.seq [ .def' "value" [] (.int 1),
            .def' "get" [] (.send none "value" [] none),
            .send (some (.str "x")) "get" [] none ])

theorem egImplicitCall_safe :
    ∀ r, ReachableResult (Machine.init egImplicitCall) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egImplicitCall, infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf, declaresName, baseDecls,
      readableClasses, reopenableClasses, defFree, defFreeAll, addRow, declsFor, sigOf, declFor,
      declOf?, tyClassNames, groundClassNames, isSelf])

/-- **With an argument the rule exists** (L171) **and no program can reach it.**
    The receiver is `self`, so the row has to be declared on the definee's class;
    `baseDecls` declares only `Integer` rows and `infer`'s `def` arm requires
    `params.isEmpty`, so nothing in the fragment can *supply* a unary row on
    `String`. The arm is therefore inert in `check` — the L157 situation — and the
    capability is asserted against `infer` directly, below. -/
example : check (.class' "String" none (.def' "g" [] (.send none "value" [.int 1] none)))
    = .unknown := by
  simp [check, infer, inferArgs, subTys, subTy, illTyped, declsOf, declaresName, baseDecls,
    readableClasses, reopenableClasses, defFree, defFreeAll, isSelf, sigOf, declFor, declOf?, declsFor,
    tyClassNames, groundClassNames]

/-- **The rule reads the row when there is one.** A `String#plus : (Integer) →
    Integer` row put in the table by hand — which is what F1c's redefinition rule
    or a `def` with parameters will eventually put there — and the receiverless
    `plus(1)` types at `Integer`. This is the whole of L171's capability, asserted
    here because the corpus cannot witness it. -/
example :
    infer (addRow baseDecls "String" "plus" { params := [Ty.int], ret := Ty.int }) []
        (.send none "plus" [.int 1] none) false
        { cls := "String", selfCls := some "String" }
      = some (Ty.int, [],
          addRow baseDecls "String" "plus" { params := [Ty.int], ret := Ty.int }) := by
  simp [infer, inferArgs, subTys, subTy, addRow, sigOf, declFor, declOf?, declsFor, baseDecls,
    tyClassNames, groundClassNames]

/-- …and **an arity mismatch is `none`**, at the same row: the whole parameter
    list is compared, so a two-argument call on a one-parameter row is refused by
    the same equality that used to compare one type against one type. -/
example :
    infer (addRow baseDecls "String" "plus" { params := [Ty.int], ret := Ty.int }) []
        (.send none "plus" [.int 1, .int 2] none) false
        { cls := "String", selfCls := some "String" }
      = none := by
  simp [infer, inferArgs, subTys, subTy, addRow, sigOf, declFor, declOf?, declsFor, baseDecls,
    tyClassNames, groundClassNames]

/-- **The class-object arm, and what it does *not* yet do** (L184). `Ty.clsOf n` is
    *the class object named `n`* — the receiver `Token.from(x)` and `case v when
    String` send to — and this asserts the two facts that make it a type language
    change rather than a rule:

    * `tyClassNames (.clsOf n) = []`, so `declFor` answers `none` at it for every
      method name and `DeclsOk` obliges nothing. That is `Ty.cls`'s exact position
      between L141 and L163, and it is deliberate: a row on `.clsOf "String"` is a
      *singleton* method while a row on `.cls "String"` is an instance method, so the
      two need different keys in one table and picking that key is rung 3's problem
      (`slice-verdict.md` §4a);
    * `TyClass` names **whatever `classOf` says**, which is L180's measurement and
      not a choice — 60 of the booted heap's 87 class objects have no materialized
      eigenclass, so *the eigenclass of the class named `n`* is not a total
      description. -/
example : declFor baseDecls (.clsOf "String") "===" = none := by
  simp [declFor, tyClassNames]

/-- …and at every name, in every table, which is what makes the arm inert. -/
example : ∀ (D : Decls) (n mname : String), declFor D (.clsOf n) mname = none := by
  intro D n mname; simp [declFor, tyClassNames]

/-- **A constant read** (L189), and the first program that gets a class-object type.

    ```ruby
    class String
      def k
        String        # ⇒ T.class_of(String)
      end
      "x".k
    end
    ```

    The rule is admitted for the eight `reopenableClasses` names and refused for
    everything else — and the eight are not a guess: `scripts/reopen_probe.lean`
    decides `ClassOk`'s seven clauses per candidate and the refusals are all
    *informative*. `Float` owns `NAN`/`INFINITY`, so nothing in front of `Object` on
    its chain is constant-free; `Array`, `Hash` and `Range` fail **sole ownership**
    because `T::Array`, `T::Hash` and `T::Range` own those names too — which is
    L177's `T` collision arriving as a refusal rather than as a hazard; `Regexp` is
    one of the two ids `invoke` dispatches a singleton family from; and
    `Comparable`/`Kernel`/`T` are modules. -/
def egConst : Expr :=
  .class' "String" none
    (.seq [ .def' "k" [] (.const "String"),
            .send (some (.str "x")) "k" [] none ])

theorem egConst_safe :
    ∀ r, ReachableResult (Machine.init egConst) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egConst, infer, inferArgs, subTys, subTy, inferSeq, inferElems, illTyped,
      illTypedAny, declsOf, declaresName, baseDecls, constTy?, baseConsts,
      readableClasses, reopenableClasses,
      groundClassNames, defFree, defFreeAll, addRow, declsFor, sigOf, declFor,
      declOf?, tyClassNames, isSelf])

/-- **And a name outside the table is `unknown`** — not typed at some guessed class.
    `Token` is a program class: it does not exist at the booted heap, so `ClassOk`
    could not promise anything about it, which is what the table's membership test
    is enforcing. -/
example : check (.class' "String" none (.def' "k" [] (.const "Token"))) = .unknown := by
  simp [check, infer, illTyped, declsOf, declaresName, baseDecls, constTy?, baseConsts,
    readableClasses, reopenableClasses,
    groundClassNames, defFree, defFreeAll, isSelf]

/-- **The class-object *producer*** (L185): `valueTy?` now gives a class object a
    type, and the facts worth asserting are which type and why the two `.ref` arms
    are disjoint.

    `String`'s class object is typed `T.class_of(String)` at the booted heap — the
    class's *own* name, not `#<Class:String>` (its eigenclass) and not `Class` (what
    `classOf` answers for a class with no eigenclass). L180 measured why it cannot
    be either: 60 of the heap's 87 class objects have no eigenclass at all. -/
example : valueTy? Boot.initHeap (.ref Boot.stringId) = some (.clsOf "String") := by
  decide

/-- **The two arms are disjoint**, because `plainRecv` refuses a `.cls` payload and
    `classRecv` requires one — so the `if` chain can never take the wrong branch. -/
example : plainRecv Boot.initHeap Boot.stringId = false := by decide

/-- **The two receiver ids `invoke` special-cases are refused** (L185), which is
    what lets `entry_dispatch`'s class case be a `simp`: `Regexp.escape`/`.quote`/
    `.union` and the `Math.sqrt`/`exp`/`log` family are singleton methods dispatched
    by receiver *id* (L106), so a type for those two objects would be a claim about
    a step the dispatch lemma does not describe. -/
example : classRecv Boot.initHeap Boot.regexpId = false := by decide

example : classRecv Boot.initHeap Boot.mathId = false := by decide

/-- **The top type as a declared parameter** (L183), which is what the arm exists
    for and the only way it can be exercised: `valueTy?` never produces `.any`, so
    nothing is *typed* by it and only a **row** can mention it.

    A hand-built row `String#plus : (T.untyped) → Integer` accepts an argument of
    any type the checker can name — here an `Integer`, a `String` and a `Symbol`
    against the same row — which is precisely what `Module#===`'s signature needs
    and what a concrete parameter cannot express (`slice-verdict.md` §4a rung 3). -/
example :
    infer (addRow baseDecls "String" "plus" { params := [Ty.any], ret := Ty.int }) []
        (.send none "plus" [.int 1] none) false
        { cls := "String", selfCls := some "String" }
      = some (Ty.int, [],
          addRow baseDecls "String" "plus" { params := [Ty.any], ret := Ty.int }) := by
  simp [infer, inferArgs, subTys, subTy, addRow, sigOf, declFor, declOf?, declsFor,
    baseDecls, tyClassNames, groundClassNames]

/-- The same row, a `String` argument. -/
example :
    infer (addRow baseDecls "String" "plus" { params := [Ty.any], ret := Ty.int }) []
        (.send none "plus" [.str "s"] none) false
        { cls := "String", selfCls := some "String" }
      = some (Ty.int, [],
          addRow baseDecls "String" "plus" { params := [Ty.any], ret := Ty.int }) := by
  simp [infer, inferArgs, subTys, subTy, addRow, sigOf, declFor, declOf?, declsFor,
    baseDecls, tyClassNames, groundClassNames]

/-- **And the arity check is untouched**: `subTys` is pointwise and length-forcing,
    so a two-argument call on a one-parameter row is still `none` — the top type
    widens a *position*, never the list. -/
example :
    infer (addRow baseDecls "String" "plus" { params := [Ty.any], ret := Ty.int }) []
        (.send none "plus" [.int 1, .int 2] none) false
        { cls := "String", selfCls := some "String" }
      = none := by
  simp [infer, inferArgs, subTys, subTy, addRow, sigOf, declFor, declOf?, declsFor,
    baseDecls, tyClassNames, groundClassNames]

/-- **Nothing is *typed* `any`**, which is the property that keeps `CtlOk` and its
    39 call sites out of this rung: `infer` never answers `.any`, so no continuation
    is ever indexed by it and no value ever carries it. Asserted at the one place a
    type could leak in — a local bound to a call on such a row gets the *return*
    type, not the parameter's. -/
example :
    infer (addRow baseDecls "String" "plus" { params := [Ty.any], ret := Ty.int }) []
        (.vasgn .lvar "q" (.send none "plus" [.int 1] none)) false
        { cls := "String", selfCls := some "String" }
      = some (Ty.int, [("q", Ty.int)],
          addRow baseDecls "String" "plus" { params := [Ty.any], ret := Ty.int }) := by
  simp [infer, inferArgs, subTys, subTy, addRow, sigOf, declFor, declOf?, declsFor,
    baseDecls, tyClassNames, groundClassNames, envSet]

/-- **A two-argument send** (L175), which was `unknown` until this rung and is the
    slice's third-largest blocker (15 method bodies). `startArgs` pushes one `argsK`
    per argument, so the rule is `inferArgs` — the argument *types* in order,
    matched against the whole parameter list — and `KontOk.argsK` carries the
    already-evaluated prefix as a `ValuesTy` beside the unevaluated tail as
    program. -/
example :
    infer (addRow baseDecls "String" "plus2"
            { params := [Ty.int, Ty.int], ret := Ty.int }) []
        (.send none "plus2" [.int 1, .int 2] none) false
        { cls := "String", selfCls := some "String" }
      = some (Ty.int, [],
          addRow baseDecls "String" "plus2" { params := [Ty.int, Ty.int], ret := Ty.int }) := by
  simp [infer, inferArgs, subTys, subTy, addRow, sigOf, declFor, declOf?, declsFor, baseDecls,
    tyClassNames, groundClassNames]

/-- **`self` in a method body**, which the same clause pays for and which is
    `unknown` in a class body — where `self` is the class object, and `plainRecv`
    gives a class no type at all. -/
def egSelf : Expr :=
  .class' "String" none (.def' "me" [] .self')

theorem egSelf_safe :
    ∀ r, ReachableResult (Machine.init egSelf) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egSelf, infer, inferArgs, subTys, subTy, declsOf, declaresName, baseDecls, readableClasses, reopenableClasses, groundClassNames,
      defFree, defFreeAll, addRow, declsFor, isSelf])

/-- **A literal `self` receiver** (L172) — `self.v`, which F1b.11 excluded and
    which is now one more uniform branch.

    ```ruby
    class String
      def v; 1; end
      def g
        self.v         # ⇒ Integer
      end
      "x".g
    end
    ```

    The exclusion was a fact about the machine: `evalExpr` picks the send *site*
    syntactically, so `self.v` is a `.selfRecv` send. `KontOk.recvK`/`recvK0` now
    take the site as a **parameter**, and the difference between the two sites is
    *permissive* — `visError?` raises only at `.explicit`, while `ResolvesAt` and
    `ResolvesUser` demand `.pub` regardless — so a public method dispatches
    identically at both and no dispatch lemma moved. `site_explicit` was withdrawn
    in the same commit, together with the `isSelf` guard it was propping up. -/
def egSelfRecv : Expr :=
  .class' "String" none
    (.seq [ .def' "v" [] (.int 1),
            .def' "g" [] (.send (some .self') "v" [] none),
            .send (some (.str "x")) "g" [] none ])

theorem egSelfRecv_safe :
    ∀ r, ReachableResult (Machine.init egSelfRecv) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egSelfRecv, infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf, declaresName, baseDecls,
      readableClasses, reopenableClasses, defFree, defFreeAll, addRow, declsFor, sigOf, declFor,
      declOf?, tyClassNames, groundClassNames, isSelf])

/-- **…and a class body still refuses it**, for the reason it always did and not
    for the guard's: in a class body `self` is the class object, `plainRecv`
    excludes a class, and `infer`'s own `self'` arm answers `none`. The receiver's
    *type* is what refuses this, not the send site. -/
example : check (.class' "String" none (.send (some .self') "upcase" [] none))
    = .unknown := by
  simp [check, infer, inferArgs, subTys, subTy, illTyped, declsOf, readableClasses, reopenableClasses, groundClassNames, isSelf, sigOf, declFor,
    declOf?, declsFor, baseDecls, tyClassNames, groundClassNames]

/-- And `self` at toplevel or in a class body is `unknown`, not accepted at some
    guessed type. -/
example : check (.class' "String" none .self') = .unknown := by
  simp [check, infer, inferArgs, subTys, subTy, illTyped, declsOf, readableClasses, reopenableClasses, groundClassNames, isSelf]

/-- **A toplevel `def` declares nothing, and the call is `unknown`** — which is
    not a limitation of the rule but of Ruby: `Interp.lean:225` makes a toplevel
    method **private**, and `ResolvesUser` requires `.pub`, so a row keyed there
    would be unwitnessable. Kept as a checked fact because it is the constraint
    that decided the rung's shape (F1b.9). -/
example : check (.seq [ .def' "shout" [] (.int 1), .vcall "shout" ]) = .unknown := by
  simp [check, infer, inferArgs, subTys, subTy, inferSeq, inferElems, illTyped, illTypedAny, declsOf, declaresName,
    baseDecls, defFree, defFreeAll, isSelf]

/-- **An array literal** (L174), and the second producer of a class-typed value.

    ```ruby
    ["a", 1 + 2]        # ⇒ Array
    ```

    `continueArray` runs the elements left to right and then `Builtins.allocArr`s
    one fresh plain `Array` — the *same* `Heap.alloc` of a non-class object L151's
    string literal makes, at `Boot.arrayId` instead of `Boot.stringId`. So the
    value half is `valueTy_alloc_fresh` again and the invariant clause is the
    second conjunct of `LitClsOk`.

    **The element types are erased**, which is what makes the rule cheap: `Ty` has
    no `Array τ`, so nothing is joined across the elements and the traversal owes
    only the environment-and-table threading — which is `inferSeq`, in the same
    left-to-right order `continueArray` uses. `KontOk.arrK` therefore does not
    mention the accumulated values at all. -/
def egArray : Expr := .array [.str "a", .send (some (.int 1)) "+" [.int 2] none]

theorem egArray_safe :
    ∀ r, ReachableResult (Machine.init egArray) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egArray, infer, inferArgs, subTys, subTy, inferSeq, inferElems, illTyped, illTypedAny, declsOf, isSelf,
      sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, groundClassNames])

/-- **The empty literal is the degenerate case, and it is a different number of
    steps**: `continueArray _ [] []` allocates immediately, with no `arrK` pushed
    at all. Worth a witness of its own for the same reason `recvK0` is a separate
    constructor from `recvK`. -/
example : check (.array []) = .accept := by
  simp [check, infer, inferArgs, subTys, subTy, inferSeq, inferElems, illTyped, declsOf]

/-- **A splat element is refused**, and by `infer` having no `.splat` arm rather
    than by a guard: `continueArray` sends a splat to `arrSplatK`, which `KontOk`
    does not describe, and the element's own `none` is what keeps the two in step. -/
example : check (.array [.splat (some (.int 1))]) = .unknown := by
  simp [check, infer, inferArgs, subTys, subTy, inferSeq, inferElems, illTyped, declsOf]

/-- `x = 0; while true do x = 1 end` — diverges, which safety permits: the
    property is *never type-stuck*, not *terminates*. -/
def egLoop : Expr :=
  .seq [ .vasgn .lvar "x" (.int 0),
         .while' .tru (.vasgn .lvar "x" (.int 1)) ]

example : check egLoop = .accept := by
  simp [check, egLoop, infer, inferArgs, subTys, subTy, inferSeq, inferElems, envSet, declsOf, isSelf]

theorem egLoop_safe : ∀ r, ReachableResult (Machine.init egLoop) r → ¬ typeStuck r :=
  check_sound (by simp [check, egLoop, infer, inferArgs, subTys, subTy, inferSeq, inferElems, envSet, declsOf, isSelf])

/-- `def f; 1 + 2; end; 3 * 4` — the P1b shape. The `def` installs a method,
    mutating the method table (which `TableOk_defineMethod` is what survives), and
    evaluates to `:f`, which the `seq` discards. -/
def egDef : Expr :=
  .seq [ .def' "f" [] (.send (some (.int 1)) "+" [.int 2] none),
         .send (some (.int 3)) "*" [.int 4] none ]

example : check egDef = .accept := by
  simp [check, egDef, infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf, declaresName, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, isSelf]

theorem egDef_safe : ∀ r, ReachableResult (Machine.init egDef) r → ¬ typeStuck r :=
  check_sound (by simp [check, egDef, infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf, declaresName, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, isSelf])

/-- `(x + 1) * 2` with `x` a local — the P0b program shape. -/
def egArith : Expr :=
  .seq [ .vasgn .lvar "x" (.int 3),
         .send (some (.send (some (.var .lvar "x")) "+" [.int 1] none))
               "*" [.int 2] none ]

example : check egArith = .accept := by
  simp [check, egArith, infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, envSet, envGet?, isSelf]

theorem egArith_safe :
    ∀ r, ReachableResult (Machine.init egArith) r → ¬ typeStuck r :=
  check_sound (by simp [check, egArith, infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, envSet, envGet?, isSelf])

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
  simp [check, egStr, infer, inferArgs, subTys, subTy, inferSeq, inferElems, envSet, envGet?, declsOf, isSelf]

theorem egStr_safe : ∀ r, ReachableResult (Machine.init egStr) r → ¬ typeStuck r :=
  check_sound (by simp [check, egStr, infer, inferArgs, subTys, subTy, inferSeq, inferElems, envSet, envGet?, declsOf, isSelf])

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
    simp [check, egStrSeq, infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf, sigOf, declFor, declOf?,
      declsFor, baseDecls, tyClassNames, envSet, envGet?, isSelf])

/-- **The first zero-argument send** (L152). `(1 + 2).zero?` is typed end to end:
    the inner send through `recvK`/`argsK` as before, the outer through the new
    `recvK0`, which dispatches in the `recvK` step itself because `startArgs … [] []`
    is `finishSend`. The result is `.bool`, so this is also the first accepted program
    whose type comes from a declaration with a return type unlike its receiver's. -/
def egZero : Expr :=
  .send (some (.send (some (.int 1)) "+" [.int 2] none)) "zero?" [] none

theorem egZero_safe : ∀ r, ReachableResult (Machine.init egZero) r → ¬ typeStuck r :=
  check_sound (by
    simp [check, egZero, infer, inferArgs, subTys, subTy, declsOf, sigOf, declFor, declOf?, declsFor,
      baseDecls, tyClassNames, isSelf])

/-- Arity is carried by the *declaration*, not by the builtin: `Integer#zero?`
    ignores its arguments entirely, and it is `baseDecls`'s `params := []` plus
    `infer`'s zero-argument arm that make this `unknown` rather than typed. -/
example : check (.send (some (.int 1)) "zero?" [.int 5] none) = .unknown := by
  simp [check, infer, inferArgs, subTys, subTy, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?,
    declsFor, baseDecls, tyClassNames, declsOf, isSelf]

/-- **`nil` on one arm is now joined** (L193), and this example is the one that
    changed: it read `unknown` from F1a through L192 and is `accept` at
    `T.nilable(Integer)` from here on. -/
example : check (.if' .tru (.int 1) (some .nil)) = .accept := by
  simp [check, infer, inferArgs, subTys, subTy, inferIf, joinTy, illTyped, declsOf, isSelf]

/-- And it really is safe, not merely accepted: `check_sound` transports through
    `joinTy` with no new hypothesis, which is the point of putting the subsumption
    in `ValueTy` and in `CtlOk`'s eval clause rather than in a narrowing rule. -/
theorem egNilJoin_safe :
    ∀ r, ReachableResult (Machine.init (.if' .tru (.int 1) (some .nil))) r →
      ¬ typeStuck r :=
  check_sound (by
    simp [check, infer, inferArgs, subTys, subTy, inferIf, joinTy, illTyped, declsOf,
      isSelf])

/-- A branch-type disagreement the fragment **still** cannot join: `unknown`, not
    `reject`. `illTyped` has no opinion about `if` arms — it only refutes calls
    the builtin table refutes — so the absence of a general union shows up as
    incompleteness rather than as a claim about the program. L193 narrowed this
    class to *neither side is `nil`*; a real union is a later rung.

    The verdict examples that *do* exercise `reject` live next to the checker
    in `Types/Core.lean`; only the safety-bearing ones belong here. -/
example : check (.if' .tru (.int 1) (some (.sym "s"))) = .unknown := by
  simp [check, infer, inferArgs, subTys, subTy, inferIf, joinTy, illTyped, declsOf, isSelf]

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
