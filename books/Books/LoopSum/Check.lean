import Books.LoopSum.Proof

/-! Build-time checks. Each fails the build if it stops holding. -/
namespace Books.LoopSum
open RubyCore RubyCore.Interp

/-! **The term is the program.** `loop_sum.json` is what the desugarer exports for
`loop_sum.rb`; decoding it must give `program 100`. -/

def exported : String := include_str "loop_sum.json"

#guard
  match Json.parse exported with
  | .ok j => (match Decode.program j with | .ok e => e == program 100 | .error _ => false)
  | .error _ => false

/-- info: 'Books.LoopSum.invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invariant

/-- info: 'Books.LoopSum.loop_sum_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_sum_invariant

/-- info: 'Books.LoopSum.here_visited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms here_visited

/-- info: 'Books.LoopSum.loop_sum_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_sum_correct

/-- info: 'Books.LoopSum.loop_sum_100' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_sum_100

end Books.LoopSum
