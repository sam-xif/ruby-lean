import Ratchet.Static.All

/-! These scalar domains do not distinguish values through first-order nominal types.
Boolean is excluded: TrueClass and FalseClass distinguish its two inhabitants. nil is
excluded: a nil-typed field may be absent, so the receiver could be frozen, and the
FrozenError path dispatches the receiver's own inspect. -/
namespace Ratchet

def scalarWriteB : Ty → Bool
  | .int | .float | .sym => true
  | _ => false

end Ratchet
