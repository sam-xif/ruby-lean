import Books.FastPower.Proof

/-!
# The one link the theorem does not cover, and the axiom audit

`fast_power_correct` is about the term `program b n`. That the term is the Ruby
program is checked here at build time: `#guard` fails the build if it is false.
-/
namespace Books.FastPower
open RubyCore RubyCore.Interp

/-! **The term is the program.** `fast_power.json` is what the desugarer exports
for `fast_power.rb`; decoding it must give `program 3 13`. -/

def exported : String := include_str "fast_power.json"

#guard
  match Json.parse exported with
  | .ok j => (match Decode.program j with | .ok e => e == program 3 13 | .error _ => false)
  | .error _ => false

/-- info: 'Books.FastPower.fast_power_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fast_power_correct

/-- info: 'Books.FastPower.fast_power_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fast_power_run

end Books.FastPower
