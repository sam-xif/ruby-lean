import Denote.Rules.Method.MethodState

/-! An uncaptured frame can still delegate locals through a for-frame alias. -/
namespace Ratchet.Denote.Typed
open RubyCore Ratchet.Denote

private def aliasedCaller : Machine :=
  { (Machine.init .nil) with
    frames := #[{ (default : RubyCore.Frame) with localAlias := some 1 },
      { (default : RubyCore.Frame) with locals := [("x", .int 7)] }]
    stack := [0] }

theorem alias_refutes_uncaptured_read : RootUncaptured aliasedCaller ∧
    aliasedCaller.getLocal "x" ≠
      (((aliasedCaller.frames.getD 0 default).locals.find? (·.1 == "x")).map (·.2)).getD .nil := by
  constructor
  · rfl
  · intro h; cases h

#guard (aliasedCaller.getLocal "x").identEq (.int 7)
#guard (aliasedCaller.frames.getD 0 default).localAlias.isSome
#print axioms alias_refutes_uncaptured_read
end Ratchet.Denote.Typed
