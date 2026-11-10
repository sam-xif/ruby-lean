import Books.TypeSoundness.Checker.Static.All

/-! These scalar domains are safe to replace with another value of the same type: every
first-order observation of the field is unchanged (`ScalarEq`,
`Conformance/Heap/ScalarPres.lean`). Two types are outside the domain, for two different
reasons.

Boolean is excluded because its two inhabitants are *distinguishable*: `TrueClass`
separates `true` from `false`, so a Boolean replacement is observable as a type.

nil is excluded for *safety*, not distinguishability. A nil-typed field may be absent, so
the receiver of a nil-field write may be a frozen object with no fields at all — which is
exactly what `StateOk.frozenFields` allows. The write then takes the model's frozen path
(`Interp.raiseFrozen`), which builds CRuby's `FrozenError` message by calling the receiver's
own `inspect` (`Interp.resumeFrozen`). That is user code, and it may raise a `TypeError`.
Every other scalar domain makes the frozen branch of `scalar_write_run` vacuous — a frozen
object has no fields, so a field of type Integer, Float or Symbol cannot be read there —
and a nil-typed field removes that argument.

The negative control `nilFieldFrozenInspect` in `Books/TypeSoundness/Controls/ScalarWriteControls.lean`
runs that program and observes the `TypeError`. The frozen branch of `scalar_write_run` is
therefore an obligation no proof can discharge by itself: it is false. Admitting nil needs a
hypothesis that rules the program out — one about the receiver's class, not about the field —
and then a `RunSpec` for the frozen write. -/
namespace Checker

def scalarWriteB : Ty → Bool
  | .int | .float | .sym => true
  | _ => false

end Checker
