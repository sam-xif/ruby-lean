import RubyCore.Interp

/-! `slow_power.rb` as a RubyCore term, with its two integer literals abstracted:
`program b n` is the program that computes `b ** n` by repeated multiplication. -/
namespace Books.FastPower.Slow
open RubyCore

/-- `left > 0` -/
abbrev condE : Expr := .send (some (.var .lvar "left")) ">" [.int 0] none
/-- `result = result * @base` -/
abbrev mulE : Expr :=
  .vasgn .lvar "result" (.send (some (.var .lvar "result")) "*" [.var .ivar "@base"] none)
/-- `left = left - 1` -/
abbrev decE : Expr :=
  .vasgn .lvar "left" (.send (some (.var .lvar "left")) "-" [.int 1] none)
/-- The loop body. -/
abbrev bodyE : Expr := .seq [mulE, decE]
/-- `while left > 0 … end` -/
abbrev loopE : Expr := .while' condE bodyE

/-- `class Power … end` -/
abbrev classE : Expr :=
  .class' "Power" none (.seq [
    .def' "initialize" [.req "base"] (.vasgn .ivar "@base" (.var .lvar "base")),
    .def' "raise_to" [.req "exponent"] (.seq [
      .vasgn .lvar "result" (.int 1),
      .vasgn .lvar "left" (.var .lvar "exponent"),
      loopE,
      .var .lvar "result"])])

/-- The whole program, for base `b` and exponent `n`. -/
def program (b : Int) (n : Nat) : Expr :=
  .seq [
    classE,
    .vasgn .lvar "power" (.send (some (.const "Power")) "new" [.int b] none),
    .vasgn .lvar "answer" (.send (some (.var .lvar "power")) "raise_to" [.int n] none),
    .send none "puts" [.var .lvar "answer"] none,
    .var .lvar "answer"]

end Books.FastPower.Slow
