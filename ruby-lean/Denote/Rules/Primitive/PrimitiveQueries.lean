import Denote.Rules.Primitive.PrimitiveStep

/-! Executable builtin equations for scalar queries. No result allocates or mutates. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem int_zero_run (m : Machine) (x : Int) :
    Builtins.run "Integer#zero?" (.int x) [] m = .ok (.bool (x == 0)) m := by
  simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
    Builtins.strPayload?, Builtins.complexEqualityImpure, Bool.false_or, Bool.or_false,
    Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem int_le_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#<=" (.int x) [.int y] m =
      .ok (.bool (compare x y != .gt)) m := by
  simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
    Builtins.strPayload?, Builtins.complexEqualityImpure, Bool.false_or, Bool.or_false,
    Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem int_ge_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#>=" (.int x) [.int y] m =
      .ok (.bool (compare x y != .lt)) m := by
  simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
    Builtins.strPayload?, Builtins.complexEqualityImpure, Bool.false_or, Bool.or_false,
    Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem nil_eq_run (m : Machine) (v : Value) :
    Builtins.run "Object#==" .nil [v] m =
      (if Builtins.complexEqualityImpure m.heap 100 v then
        .unsupported "Complex equality requires effectful component/collection dispatch"
       else .ok (.bool (Value.nil.identEq v)) m) := by
  simp only [Builtins.run,
    show Builtins.byteStrAwareBids.contains "Object#==" = true from rfl,
    show "Object#==".endsWith "#==" = true from by decide +kernel,
    Bool.true_or, List.any_cons, List.any_nil, Builtins.complexEqualityImpure,
    Bool.false_or, Bool.or_false,
    Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem string_length_run (m : Machine) (v : Value) :
    Builtins.run "String#length" v [] m = Builtins.runStrings "String#length" v [] m := by
  simp only [Builtins.run,
    show Builtins.byteStrAwareBids.contains "String#length" = true from rfl,
    show ("String#length".endsWith "#==" || "String#length".endsWith "#eql?" ||
      "String#length".endsWith "#!=" || Builtins.pureEqualityBids.contains "String#length") = false from by decide +kernel,
    Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

#print axioms nil_eq_run
#print axioms string_length_run
end Ratchet.Denote.Typed
