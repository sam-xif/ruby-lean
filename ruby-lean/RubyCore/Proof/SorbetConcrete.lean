/-
Concrete Sorbet-safety certificates: the machinery of `SorbetSafety.lean` applied
to real programs from `difftest/corpus/sorbet/`, whose behavior is pinned against
the actual `sorbet-runtime` gem by the difftest ratchet.

These are **Direction A** (`AGENTS.md` §Type safety as reachability §3): the certificate
is the trace. No invariant, no SMT — run the trusted stepper and read the
outcome. What is new here relative to `T5Concrete.lean` is the middle case: a
run that ends in **blame** is a *pass*, because sorbet-runtime raising at a sig
boundary is the type system working, not the program going wrong.

Every run starts from the **prelude-booted** heap, because sig enforcement lives
in the `T` shim (L80). `native_decide` carries the concrete executions, as in
`T5Concrete.lean`; the metatheorems in `SorbetSafety.lean` stay axiom-clean.

JSON literals are `desugar-dt/bin/export-json` output for the named
corpus sources — regenerate them if those sources change.
-/
import RubyCore.Proof.SorbetSafety
import RubyCore.Proof.RunCert

namespace RubyCore
namespace Proof
namespace SorbetConcrete

open Interp
-- `Json` is this project's vendored copy of Lean's (`Json.lean`), at the root
-- namespace, so there is nothing to open.

/-! ## Decidable drivers (prelude-booted) -/

/-- Bool mirror of `isBlame`. -/
def isBlameB (h : Heap) (exc : Value) : Bool :=
  isA h exc Boot.typeErrorId && blamePrefixes.any (fun p => p.isPrefixOf (excMessage h exc))

theorem isBlameB_iff (h : Heap) (exc : Value) : isBlameB h exc = true ↔ isBlame h exc := by
  simp [isBlameB, isBlame, List.any_eq_true]

/-- Parse, decode, **boot the prelude**. `none` when any of those fail — a
    decode or prelude failure is a model/harness bug, never a program verdict. -/
def bootOf (js : String) : Option Machine :=
  match Json.parse js with
  | .error _ => none
  | .ok j => match Decode.program j with
    | .error _ => none
    | .ok e => (Prelude.initWithPrelude e).toOption

/-- The run terminates in a value. -/
def runsToValueBooted (js : String) (fuel : Nat) : Bool :=
  match bootOf js with
  | none => false
  | some m0 => match run fuel m0 with
    | .value _ _ => true
    | _ => false

/-- The run ends in **blame** — a sig/assertion boundary check firing. -/
def runsToBlameBooted (js : String) (fuel : Nat) : Bool :=
  match bootOf js with
  | none => false
  | some m0 => match run fuel m0 with
    | .uncaught exc m => isBlameB m.heap exc
    | _ => false

/-- The run ends in a type-family error that is **not** blame: a counterexample
    to Sorbet-safety, witnessed by the trace. -/
def runsToSorbetStuckBooted (js : String) (fuel : Nat) : Bool :=
  match bootOf js with
  | none => false
  | some m0 => match run fuel m0 with
    | .uncaught exc m => isTypeErrorB m.heap exc && !isBlameB m.heap exc
    | _ => false

/-! ## Bridges from the drivers to the property -/

theorem runsToValueBooted_safe {js : String} {fuel : Nat}
    (h : runsToValueBooted js fuel = true) :
    ∃ m₀, ∃ r, ReachableResult m₀ r ∧ ¬ sorbetStuck r := by
  unfold runsToValueBooted at h
  cases hb : bootOf js with
  | none => rw [hb] at h; simp at h
  | some m0 =>
    rw [hb] at h
    cases hr : run fuel m0 with
    | value v mf => exact ⟨m0, run_value_sorbet_safe hr⟩
    | uncaught _ _ => simp [hr] at h
    | unsupported _ _ => simp [hr] at h
    | outOfFuel _ => simp [hr] at h
    | stuck _ _ => simp [hr] at h

theorem runsToBlameBooted_safe {js : String} {fuel : Nat}
    (h : runsToBlameBooted js fuel = true) :
    ∃ m₀, ∃ r, ReachableResult m₀ r ∧ ¬ sorbetStuck r := by
  unfold runsToBlameBooted at h
  cases hb : bootOf js with
  | none => rw [hb] at h; simp at h
  | some m0 =>
    rw [hb] at h
    cases hr : run fuel m0 with
    | uncaught exc mf =>
      simp only [hr] at h
      exact ⟨m0, run_blame_sorbet_safe hr ((isBlameB_iff mf.heap exc).mp h)⟩
    | value _ _ => simp [hr] at h
    | unsupported _ _ => simp [hr] at h
    | outOfFuel _ => simp [hr] at h
    | stuck _ _ => simp [hr] at h

theorem runsToSorbetStuckBooted_unsafe {js : String} {fuel : Nat}
    (h : runsToSorbetStuckBooted js fuel = true) :
    ∃ m₀, ¬ SorbetSafeFrom m₀ := by
  unfold runsToSorbetStuckBooted at h
  cases hb : bootOf js with
  | none => rw [hb] at h; simp at h
  | some m0 =>
    rw [hb] at h
    cases hr : run fuel m0 with
    | uncaught exc mf =>
      simp only [hr, Bool.and_eq_true, Bool.not_eq_true'] at h
      refine ⟨m0, run_sorbetStuck_unsafe hr ((isTypeErrorB_iff mf.heap exc).mp h.1) ?_⟩
      intro hbl
      have : isBlameB mf.heap exc = true := (isBlameB_iff mf.heap exc).mpr hbl
      rw [this] at h
      simp at h
    | value _ _ => simp [hr] at h
    | unsupported _ _ => simp [hr] at h
    | outOfFuel _ => simp [hr] at h
    | stuck _ _ => simp [hr] at h

/-! ## The certificates -/

/-- `corpus/sorbet/sig-basic/000.rb` — a correctly annotated class. -/
def sigBasic000 : String :=
"{\"v\":4,\"ast\":[\"seq\",[\"send\",null,\"require\",[[\"str\",\"sorbet-runtime\"]],null],[\"class\",\"Greeter\",null,[\"seq\",[\"send\",null,\"extend\",[[\"cpath\",[\"const\",\"T\"],\"Sig\"]],null],[\"send\",null,\"sig\",[],[\"block\",[],[],[\"send\",[\"send\",null,\"params\",[[\"kwargs\",[[[\"sym\",\"name\"],[\"const\",\"String\"]]]]],null],\"void\",[],null]]],[\"def\",\"initialize\",[[\"preq\",\"name\"]],[\"vasgn\",\"ivar\",\"@name\",[\"send\",[\"const\",\"T\"],\"let\",[[\"var\",\"local\",\"name\"],[\"const\",\"String\"]],null]]],[\"send\",null,\"sig\",[],[\"block\",[],[],[\"send\",null,\"returns\",[[\"const\",\"String\"]],null]]],[\"def\",\"greet\",[],[\"send\",[\"str\",\"hello, \"],\"+\",[[\"seq\",[\"vasgn\",\"local\",\"__dt_t1\",[\"var\",\"ivar\",\"@name\"]],[\"if\",[\"send\",[\"const\",\"String\"],\"===\",[[\"var\",\"local\",\"__dt_t1\"]],null],[\"var\",\"local\",\"__dt_t1\"],[\"send\",[\"var\",\"local\",\"__dt_t1\"],\"to_s\",[],null]]]],null]]]],[\"send\",null,\"puts\",[[\"send\",[\"send\",[\"const\",\"Greeter\"],\"new\",[[\"str\",\"world\"]],null],\"greet\",[],null]],null]]}\n"

/-- `corpus/sorbet/sig-basic/001.rb` — a sig violated at a call site; the
    runtime wrapper raises. -/
def sigBasic001 : String :=
"{\"v\":4,\"ast\":[\"seq\",[\"send\",null,\"require\",[[\"str\",\"sorbet-runtime\"]],null],[\"send\",null,\"extend\",[[\"cpath\",[\"const\",\"T\"],\"Sig\"]],null],[\"send\",null,\"sig\",[],[\"block\",[],[],[\"send\",[\"send\",null,\"params\",[[\"kwargs\",[[[\"sym\",\"x\"],[\"const\",\"Integer\"]]]]],null],\"returns\",[[\"const\",\"String\"]],null]]],[\"def\",\"stringify\",[[\"preq\",\"x\"]],[\"send\",[\"var\",\"local\",\"x\"],\"to_s\",[],null]],[\"send\",null,\"puts\",[[\"send\",null,\"stringify\",[[\"int\",1]],null]],null],[\"send\",null,\"puts\",[[\"send\",null,\"stringify\",[[\"str\",\"two\"]],null]],null]]}\n"

/-- `corpus/sorbet/untyped-boundary/000.rb` — no sigs at all, so Sorbet permits
    a send that does not exist. -/
def untypedBoundary000 : String :=
"{\"v\":4,\"ast\":[\"seq\",[\"send\",null,\"require\",[[\"str\",\"sorbet-runtime\"]],null],[\"def\",\"apply\",[[\"preq\",\"f\"],[\"preq\",\"x\"]],[\"send\",[\"var\",\"local\",\"f\"],\"call\",[[\"var\",\"local\",\"x\"]],null]],[\"def\",\"call_missing\",[[\"preq\",\"obj\"]],[\"send\",[\"var\",\"local\",\"obj\"],\"no_such_method\",[],null]],[\"send\",null,\"puts\",[[\"send\",null,\"apply\",[[\"send\",null,\"lambda\",[],[\"block\",[[\"preq\",\"n\"]],[],[\"send\",[\"var\",\"local\",\"n\"],\"+\",[[\"int\",1]],null]]],[\"int\",1]],null]],null],[\"send\",null,\"puts\",[[\"send\",null,\"call_missing\",[[\"int\",3]],null]],null]]}\n"


theorem sigBasic000_runs_to_value : runsToValueBooted sigBasic000 200000 = true := by
  native_decide

/-- **Certified Sorbet-safe by execution** (for this input). -/
theorem sigBasic000_sorbet_safe :
    ∃ m₀, ∃ r, ReachableResult m₀ r ∧ ¬ sorbetStuck r :=
  runsToValueBooted_safe sigBasic000_runs_to_value

theorem sigBasic001_blames : runsToBlameBooted sigBasic001 200000 = true := by
  native_decide

/-- **Blame is a pass.** The run ends in an uncaught `TypeError` — a *type-stuck*
    outcome as far as `TypeSafety.lean` is concerned — and is nonetheless
    Sorbet-safe, because the exception is enforcement firing at the boundary.
    This one theorem is the entire content of the weakened bad state. -/
theorem sigBasic001_sorbet_safe :
    ∃ m₀, ∃ r, ReachableResult m₀ r ∧ ¬ sorbetStuck r :=
  runsToBlameBooted_safe sigBasic001_blames

theorem untypedBoundary000_stuck : runsToSorbetStuckBooted untypedBoundary000 200000 = true := by
  native_decide

/-- The counterexample direction: an unsigned program `srb` accepts, reaching an
    uncaught `NoMethodError` that is not blame. Excluded from the fragment for
    exactly this reason (`Types/Fragment.lean`, criterion 2) — so this refutes
    Sorbet-safety without refuting anything the fragment claims. -/
theorem untypedBoundary000_not_sorbet_safe : ∃ m₀, ¬ SorbetSafeFrom m₀ :=
  runsToSorbetStuckBooted_unsafe untypedBoundary000_stuck

end SorbetConcrete
end Proof
end RubyCore
