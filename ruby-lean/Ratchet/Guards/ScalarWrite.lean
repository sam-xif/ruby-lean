import Ratchet.Static.All

/-! These scalar domains do not distinguish values through first-order nominal types.
Boolean is excluded: TrueClass and FalseClass distinguish its two inhabitants. -/
namespace Ratchet

def scalarWriteB : Ty → Bool
  | .int | .float | .sym | .nilT => true
  | _ => false

end Ratchet
