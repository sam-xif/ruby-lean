import Checker.Check.Check
import Books.TypeSoundness.Conformance.Core.Boot

/-! The *statements* of the validator's end-to-end safety theorems, with no proofs.

This is the trusted half of a `leanprover/comparator` run (`scripts/run-comparator.sh`):
the comparator exports these three statements and the same-named theorems of
`Books/TypeSoundness/Soundness.lean`, checks that the statements and every constant they mention are
identical in both environments, that the proofs in `Books.TypeSoundness.Soundness` use only the permitted
axioms, and replays the proofs' whole dependency closure through the Lean kernel.

Keep the statements here textually identical to `Books/TypeSoundness/Soundness.lean`'s. The imports are
the ones the statements need (`validateD`; `StateOk`, `StuckFree`, `bootOkB`,
`bootMachine`, `Semantics.run`) and deliberately not `Books.TypeSoundness.Registry.AuditBridge`, which is
where the proof comes from. Off the default build target: it is `sorry` by design. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem validateD_safe {p : Checker.Expr} {d : Deriv}
    (h : validateD p d = true)
    {m : Machine} (hm : StateOk ctx0 [] .ivar0 m) : StuckFree m p := sorry

theorem validateD_safe_boot {p : Checker.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) :
    StuckFree bootMachine p := sorry

theorem validateD_safe_run {p : Checker.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false := sorry

end Checker.Soundness.Typed
