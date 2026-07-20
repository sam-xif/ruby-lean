/-
Run-certificate bridges (Direction A of `type-safety-by-reachability.md` §3):
turn a *decidable boolean* about a program's concrete run into a type-safety
verdict (or its refutation). These bridges are **axiom-clean**; the boolean they
consume is discharged per program by `native_decide` in a separate, opt-in file
(`T5Concrete.lean`, `QLearningTypeSafe.lean`) — that is where the compiler enters
the trust base, never here.

- `runsToValueB js fuel = true`  ⇒  the program is type-safe (reaches a value,
  never a type-family `uncaught`).                        [prove direction]
- `runsToTypeErrorB js fuel = true` ⇒ the program is NOT type-safe (a type-stuck
  outcome is reachable; the run is the counterexample).   [disprove direction]

`js` is the desugared+linked RubyCore export JSON (`bin/export-json`).
-/
import RubyCore.Proof.TypeSafety

namespace RubyCore
namespace Proof

open Interp Lean

/-- Decidable mirror of `isTypeError` (family membership via `isA`). -/
def isTypeErrorB (h : Heap) (exc : Value) : Bool :=
  typeErrorFamily.any (fun k => isA h exc k)

theorem isTypeErrorB_iff (h : Heap) (exc : Value) :
    isTypeErrorB h exc = true ↔ isTypeError h exc := by
  unfold isTypeErrorB isTypeError
  simp [List.any_eq_true]

/-- Parse + decode + run, reporting whether the run terminates in a value. -/
def runsToValueB (js : String) (fuel : Nat) : Bool :=
  match Json.parse js with
  | .error _ => false
  | .ok j => match Decode.program j with
    | .error _ => false
    | .ok e => match run fuel (Machine.init e) with
      | .value _ _ => true
      | _ => false

/-- Parse + decode + run, reporting whether the run ends in an uncaught
    *type-family* exception. -/
def runsToTypeErrorB (js : String) (fuel : Nat) : Bool :=
  match Json.parse js with
  | .error _ => false
  | .ok j => match Decode.program j with
    | .error _ => false
    | .ok e => match run fuel (Machine.init e) with
      | .uncaught exc m => isTypeErrorB m.heap exc
      | _ => false

/-- **Prove bridge.** `runsToValueB = true` ⇒ the decoded program is type-safe:
    no reachable outcome is type-stuck. -/
theorem runsToValueB_type_safe {js : String} {fuel : Nat}
    (h : runsToValueB js fuel = true) :
    ∃ e : Expr, ∃ r, ReachableResult (Machine.init e) r ∧ ¬ typeStuck r := by
  unfold runsToValueB at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i e _
      split at h
      · rename_i v m hrun
        exact ⟨e, run_value_type_safe hrun⟩
      · simp at h

/-- **Disprove bridge.** `runsToTypeErrorB = true` ⇒ the decoded program is NOT
    type-safe: a type-stuck outcome is reachable (the run is the counterexample). -/
theorem runsToTypeErrorB_unsafe {js : String} {fuel : Nat}
    (h : runsToTypeErrorB js fuel = true) :
    ∃ e : Expr, ∃ r, ReachableResult (Machine.init e) r ∧ typeStuck r := by
  unfold runsToTypeErrorB at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i e _
      split at h
      · rename_i exc m hrun
        exact ⟨e, run_typeError_unsafe hrun ((isTypeErrorB_iff m.heap exc).mp h)⟩
      · simp at h

end Proof
end RubyCore
