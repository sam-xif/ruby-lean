import Books.FastPower.Faster

/-!
# The one link the theorems do not cover, and the axiom audit

The theorems are about the terms `Slow.program b n` and `Fast.program b n`. That
those terms are the Ruby programs is checked here at build time: `#guard` fails
the build if it is false.
-/
namespace Books.FastPower
open RubyCore RubyCore.Interp

/-- Does `json`, as the desugarer exports it, decode to `program`? -/
def exports (json : String) (program : Expr) : Bool :=
  match Json.parse json with
  | .ok j => (match Decode.program j with | .ok e => e == program | .error _ => false)
  | .error _ => false

/-! **The terms are the programs.** Each `.json` is what the desugarer exports
for the `.rb` beside it, whose literals are base 3 and exponent 13. -/

#guard exports (include_str "slow_power.json") (Slow.program 3 13)
#guard exports (include_str "fast_power.json") (Fast.program 3 13)

/-- info: 'Books.FastPower.slow_computes_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slow_computes_power

/-- info: 'Books.FastPower.fast_computes_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fast_computes_power

/-- info: 'Books.FastPower.Slow.computes_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Slow.computes_power

/-- info: 'Books.FastPower.Fast.computes_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fast.computes_power

/-- info: 'Books.FastPower.fast_is_faster' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fast_is_faster

end Books.FastPower
