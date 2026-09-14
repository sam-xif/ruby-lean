import Denote.Typed.PrimitiveStep

/-! Executable builtin equations for scalar queries. No result allocates or mutates. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem int_zero_run (m : Machine) (x : Int) :
    Builtins.run "Integer#zero?" (.int x) [] m = .ok (.bool (x == 0)) m := by rfl

theorem int_le_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#<=" (.int x) [.int y] m =
      .ok (.bool (compare x y != .gt)) m := by rfl

theorem int_ge_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#>=" (.int x) [.int y] m =
      .ok (.bool (compare x y != .lt)) m := by rfl

theorem nil_eq_run (m : Machine) (v : Value) :
    Builtins.run "Object#==" .nil [v] m = .ok (.bool (Value.nil.identEq v)) m := by
  simp only [Builtins.run,
    show Builtins.byteStrAwareBids.contains "Object#==" = true from rfl,
    Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem string_length_run (m : Machine) (v : Value) :
    Builtins.run "String#length" v [] m = Builtins.runStrings "String#length" v [] m := by
  simp only [Builtins.run,
    show Builtins.byteStrAwareBids.contains "String#length" = true from rfl,
    Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

#print axioms nil_eq_run
#print axioms string_length_run
end Ratchet.Denote.Typed
