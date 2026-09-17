/-
Type safety as reachability — the metatheory that turns the executable
semantics into a *type-safety checker* (`AGENTS.md` §Type safety as reachability §4,
Direction B). "Typed" is not a separate system: a program is type-safe iff the
set of **type-stuck outcomes** is unreachable from `Machine.init` under the
machine's own transition relation.

This file authors, over the semantics itself:

  1. `typeStuck` / `aboutToTypeStick` — the bad-state predicate, grounded in
     `StepResult` filtered by the type-error class family (`type-safety-by-
     reachability.md` §2): NoMethodError ∪ ArgumentError ∪ TypeError, closed
     under subclassing (via `isA`).
  2. `SmallStep` / `Reaches` / `ReachableResult` — the transition relation and
     its reflexive-transitive closure.  **`SmallStep m m' := stepFn m = .next
     m'` is the FULL transition relation** — the executable interpreter *is* a
     small-step relation (each `stepFn` call is one transition; see the header
     of `Interp.lean`).  Reachability must range over the full relation, not the
     partial control-core inductive `Step` of `Step.lean`: a subset relation
     reaches *fewer* states, so safety over it would not transfer to the real
     machine.  Formulating over `stepFn` is therefore both the sound choice and
     the reason this metatheorem applies to *every* program the interpreter runs
     — including the `q_learning_extended` demo, which `stepFn` executes to a
     value (see `Direction A` below).
  3. `invariant_sound` — the progress/preservation metatheorem: any inductive
     invariant `I` satisfying Initiation / Consecution (preservation) / Safety
     (progress-to-not-stuck) proves *no reachable outcome is type-stuck*, for
     all inputs and unbounded fuel.  Proved once; per program the (untrusted)
     search engine supplies `I` and the (trusted, tiny) validator re-checks the
     three local conditions.  See `AGENTS.md` §Type safety as reachability §4.
  4. `Step.subset_smallStep` — the bridge: the control-core inductive `Step` is
     a sub-relation of `SmallStep` (this is exactly `Step.sound`), so any
     relational reasoning done via `Step`'s constructors transfers to the
     metatheorem.
  5. Direction A (§3): a run that terminates in a *value* is a self-certifying,
     zero-proof type-safety certificate *for that input* — the outcome is
     `done`, never a type-family `uncaught`.  `run_value_reaches_done` connects
     the fuel iterator `run` to `ReachableResult`, so an execution witness is a
     machine-level proof of type-safety of that concrete run.  For
     `q_learning_extended` the witness is produced by *running* the interpreter
     (`bin/demo-qlearning --extended` — the model executes it to a value,
     byte-for-byte with CRuby): dispatch bottoms out in `invoke`, a well-founded
     `def` (`Acc.rec`) that the kernel's whnf does not reduce, so the certificate
     for a real program is obtained by execution of the trusted stepper (the
     whole point of Direction A: "the certificate is the trace"), not by an
     in-kernel `rfl` (see `QLearningTypeSafe.lean`).

Axiom audit target (see `implementation-notes.md` L13): `propext` /
`Classical.choice` / `Quot.sound` only — no `sorryAx`, no `native_decide`.
-/
import RubyCore.Proof.Step

namespace RubyCore
namespace Proof

open Interp

/-! ## 1. The bad-state predicate (`AGENTS.md` §Type safety as reachability §2) -/

/-- The type-error exception family (`AGENTS.md` §Type safety as reachability §2):
    NoMethodError, ArgumentError, TypeError.  Membership is tested with `isA`,
    so the family is automatically **closed under subclassing** (a user
    `class MyTypeError < TypeError` still counts). -/
def typeErrorFamily : List ObjId :=
  [Boot.noMethodErrorId, Boot.argumentErrorId, Boot.typeErrorId]

/-- A raised exception value `exc` is a type error iff its class `isA` some
    member of the family.  Note NoMethodError ⊂ NameError but the family lists
    NoMethodError specifically: a *bare* NameError (undefined constant/var) is
    deliberately NOT flagged here — its ancestor chain contains neither
    NoMethodError nor ArgumentError nor TypeError. -/
def isTypeError (h : Heap) (exc : Value) : Prop :=
  ∃ k ∈ typeErrorFamily, isA h exc k = true

/-- **The bad state as a terminal outcome** (`AGENTS.md` §Type safety as reachability
    §2, "raised ≠ stuck"): a run is *type-stuck* only when a type-family
    exception **escapes to the toplevel** (`uncaught`).  A `NoMethodError` that a
    `rescue` catches is a transient `raiseJ` that never becomes an `uncaught`
    outcome — such a program is type-safe.  This is strictly more faithful than a
    type system, which cannot see a locally-caught raise. -/
def typeStuck : StepResult → Prop
  | .uncaught exc m => isTypeError m.heap exc
  | _ => False

/-- A config is *about to type-stick* iff its single next transition is a
    type-stuck terminal outcome.  This is the `¬ aboutToTypeStick` obligation
    the invariant's Safety condition discharges — the progress half of
    progress/preservation. -/
def aboutToTypeStick (m : Machine) : Prop := typeStuck (stepFn m)

/-! ## 2. The transition relation and its reflexive-transitive closure -/

/-- **The full small-step transition relation.**  `stepFn` is total and each
    call is exactly one transition, so this relation is the executable semantics
    viewed as a relation — no separate inductive rendering needed for the
    metatheorem, and it covers every construct the interpreter models. -/
def SmallStep (m m' : Machine) : Prop := stepFn m = .next m'

/-- Reflexive-transitive closure of `SmallStep`: "reaches in finitely many
    steps." -/
inductive Reaches : Machine → Machine → Prop where
  | refl {m} : Reaches m m
  | tail {m₁ m₂ m₃} : Reaches m₁ m₂ → SmallStep m₂ m₃ → Reaches m₁ m₃

/-- Prepend a single step to a chain (`Reaches` grows at the tail, so a
    front-step needs this induction). -/
theorem Reaches.head {m₁ m₂ m₃ : Machine}
    (hstep : SmallStep m₁ m₂) (hr : Reaches m₂ m₃) : Reaches m₁ m₃ := by
  induction hr with
  | refl => exact .tail .refl hstep
  | tail _ hs ih => exact .tail ih hs

/-- A terminal `StepResult` reachable from `m₀`: run to some reachable config
    `m`, then take its (terminal — `done`/`uncaught`/`unsupported`/`stuck`) step.
    (`typeStuck` only holds of `uncaught`, so the terminality is implicit.) -/
def ReachableResult (m₀ : Machine) (r : StepResult) : Prop :=
  ∃ m, Reaches m₀ m ∧ stepFn m = r

/-! ## 3. The metatheorem (`AGENTS.md` §Type safety as reachability §4, Direction B) -/

/-- An invariant holds at every config reachable from a config where it holds —
    the preservation step lifted along the RT-closure. -/
theorem invariant_reaches {I : Machine → Prop}
    (cons : ∀ m m', I m → SmallStep m m' → I m')
    {m₀ m : Machine} (hI : I m₀) (hr : Reaches m₀ m) : I m := by
  induction hr with
  | refl => exact hI
  | tail _ hstep ih => exact cons _ _ ih hstep

/-- **Type safety by invariant (progress/preservation).**  Any inductive
    invariant `I` with

      Initiation:   `I (Machine.init program)`
      Consecution:  `∀ m m', I m → SmallStep m m' → I m'`   (preservation)
      Safety:       `∀ m, I m → ¬ aboutToTypeStick m`       (progress)

    proves **no reachable outcome is type-stuck** — for all inputs, unbounded
    fuel.  This is the one-time metatheorem of `AGENTS.md` §Type safety as reachability
    §4: it says nothing about any checker.  Per program, an untrusted engine
    emits some concrete `I`; the trusted validator only re-checks
    `init`/`cons`/`safe` for that `I`, and this theorem does the rest.

    Because `SmallStep`/`Reaches` range over the *full* `stepFn` relation, the
    statement is meaningful for arbitrary real programs (dispatch, classes,
    blocks, …), not only the control-core fragment of `Step.lean`. -/
theorem invariant_sound_from {m₀ : Machine} (I : Machine → Prop)
    (init : I m₀)
    (cons : ∀ m m', I m → SmallStep m m' → I m')
    (safe : ∀ m, I m → ¬ aboutToTypeStick m) :
    ∀ r, ReachableResult m₀ r → ¬ typeStuck r := by
  rintro r ⟨m, hr, hstep⟩ hts
  have hIm : I m := invariant_reaches cons init hr
  exact safe m hIm (by unfold aboutToTypeStick; rw [hstep]; exact hts)

/-- **Every reachable result satisfies whatever the invariant forces of a single
    step** (L271) — `invariant_sound_from` generalized from `¬ typeStuck` to an
    arbitrary result predicate `P`. A reachable result *is* `stepFn m` at some
    invariant-satisfying `m`, so `P` needs establishing only there. This is the
    composition point for conclusions beyond safety: the J29 answer-typed
    `StepOkJ` puts `VTy mf.heap v ans` in its `done` arm, and this lemma is what
    carries that to every reachable `done` outcome (`SemJudge`'s result clause,
    `judge_result_vty`). -/
theorem invariant_result_sound {m₀ : Machine} (I : Machine → Prop)
    (init : I m₀)
    (cons : ∀ m m', I m → SmallStep m m' → I m')
    {P : StepResult → Prop} (hstep : ∀ m, I m → P (stepFn m)) :
    ∀ r, ReachableResult m₀ r → P r := by
  rintro r ⟨m, hr, hs⟩
  have := hstep m (invariant_reaches cons init hr)
  rwa [hs] at this

/-- `invariant_sound` from the program's initial config — the special case of
    `invariant_sound_from` at `m₀ = Machine.init program`. -/
theorem invariant_sound {program : Expr} (I : Machine → Prop)
    (init : I (Machine.init program))
    (cons : ∀ m m', I m → SmallStep m m' → I m')
    (safe : ∀ m, I m → ¬ aboutToTypeStick m) :
    ∀ r, ReachableResult (Machine.init program) r → ¬ typeStuck r :=
  invariant_sound_from I init cons safe

/-! ## 4. The bridge to the inductive control-core `Step` -/

/-- The control-core inductive `Step` (`Step.lean`) is a sub-relation of the
    full `SmallStep` — this is exactly `Step.sound`.  So an invariant argument
    carried out relationally over `Step`'s constructors (idiomatic case
    analysis) discharges the corresponding `SmallStep` obligation. -/
theorem Step.subset_smallStep {m m' : Machine} (h : Step m m') : SmallStep m m' :=
  h.sound

/-! ## 5. Direction A — the execution certificate (`§3`)

    A concrete run that terminates in a value is a self-certifying, zero-proof
    type-safety witness *for that input*: `stepFn` reaches a `done` outcome,
    which is not `typeStuck`.  This is what `bin/demo-qlearning --extended`
    produces for `q_learning_extended.rb` — the model runs it to completion
    (matching CRuby byte-for-byte), so that run is certified type-safe. -/

/-- Fuel-iterating `run` to a value means: some reachable config takes a `done`
    step.  (Induction on fuel; `run` just chases `SmallStep` edges.) -/
theorem run_value_reaches_done {fuel : Nat} {m₀ : Machine} {v : Value} {mf : Machine}
    (h : run fuel m₀ = .value v mf) :
    ReachableResult m₀ (.done v mf) := by
  induction fuel generalizing m₀ with
  | zero => simp [run] at h
  | succ n ih =>
    rw [run] at h
    -- split on this step's result; only `.next` (recurse) and `.done` (base) survive
    cases hs : stepFn m₀ with
    | next m' =>
      rw [hs] at h
      obtain ⟨m, hr, hstep⟩ := ih h
      exact ⟨m, Reaches.head hs hr, hstep⟩
    | done v' m' => rw [hs] at h; injection h with hv hm; subst hv; subst hm
                    exact ⟨m₀, .refl, hs⟩
    | uncaught e m' => rw [hs] at h; exact absurd h (by simp)
    | unsupported r => rw [hs] at h; exact absurd h (by simp)
    | stuck msg => rw [hs] at h; exact absurd h (by simp)

/-- A `done` outcome is never type-stuck: a run that terminates in a value is a
    type-safety certificate for that input (Direction A, §3). -/
theorem done_not_typeStuck {v : Value} {m : Machine} : ¬ typeStuck (.done v m) := by
  intro h; exact h

/-- **Execution certificate.**  If a program's run terminates in a value, that
    execution reaches a non-type-stuck terminal outcome — the self-certifying
    Direction-A witness, no invariant required.  (For `q_learning_extended`,
    `bin/demo-qlearning --extended` exhibits exactly such a terminating run.) -/
theorem run_value_type_safe {program : Expr} {fuel : Nat} {v : Value} {mf : Machine}
    (h : run fuel (Machine.init program) = .value v mf) :
    ∃ r, ReachableResult (Machine.init program) r ∧ ¬ typeStuck r :=
  ⟨.done v mf, run_value_reaches_done h, done_not_typeStuck⟩

/-! ### Disprove direction: an execution that ends in an uncaught exception -/

/-- Dual of `run_value_reaches_done` for the `uncaught` outcome: a run that ends
    with an uncaught exception reaches that `.uncaught` StepResult. -/
theorem run_uncaught_reaches {m₀ : Machine} {fuel : Nat} {exc : Value} {mf : Machine}
    (h : run fuel m₀ = .uncaught exc mf) :
    ReachableResult m₀ (.uncaught exc mf) := by
  induction fuel generalizing m₀ with
  | zero => simp [run] at h
  | succ n ih =>
    rw [run] at h
    cases hs : stepFn m₀ with
    | next m' =>
      rw [hs] at h
      obtain ⟨m, hr, hstep⟩ := ih h
      exact ⟨m, Reaches.head hs hr, hstep⟩
    | done v' m' => rw [hs] at h; exact absurd h (by simp)
    | uncaught e m' => rw [hs] at h; injection h with he hm; subst he; subst hm
                       exact ⟨m₀, .refl, hs⟩
    | unsupported r => rw [hs] at h; exact absurd h (by simp)
    | stuck msg => rw [hs] at h; exact absurd h (by simp)

/-- **Counterexample certificate (disprove direction).**  If a program's run
    ends in an uncaught *type-family* exception, the program is NOT type-safe:
    a type-stuck outcome is reachable.  The run trace is the counterexample
    (Direction A, §3 — "the certificate is the trace"), witnessing the negation
    of the safety property `∀ r, ReachableResult … → ¬ typeStuck r`. -/
theorem run_typeError_unsafe {program : Expr} {fuel : Nat} {exc : Value} {mf : Machine}
    (h : run fuel (Machine.init program) = .uncaught exc mf)
    (hte : isTypeError mf.heap exc) :
    ∃ r, ReachableResult (Machine.init program) r ∧ typeStuck r :=
  ⟨.uncaught exc mf, run_uncaught_reaches h, hte⟩

end Proof
end RubyCore
