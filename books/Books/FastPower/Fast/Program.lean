import RubyCore.Interp

/-! `fast_power.rb` as a RubyCore term, with its two integer literals abstracted:
`program b n` is the program that computes `b ** n` by squaring. -/
namespace Books.FastPower.Fast
open RubyCore

/-- `left > 0` -/
abbrev condE : Expr := .send (some (.var .lvar "left")) ">" [.int 0] none
/-- `left % 2 == 1` -/
abbrev oddE : Expr :=
  .send (some (.send (some (.var .lvar "left")) "%" [.int 2] none)) "==" [.int 1] none
/-- `result = result * square` -/
abbrev mulE : Expr :=
  .vasgn .lvar "result" (.send (some (.var .lvar "result")) "*" [.var .lvar "square"] none)
/-- `square = square * square` -/
abbrev squareE : Expr :=
  .vasgn .lvar "square" (.send (some (.var .lvar "square")) "*" [.var .lvar "square"] none)
/-- `left = left / 2` -/
abbrev halveE : Expr :=
  .vasgn .lvar "left" (.send (some (.var .lvar "left")) "/" [.int 2] none)
/-- The loop body. -/
abbrev bodyE : Expr := .seq [.if' oddE mulE none, squareE, halveE]
/-- `while left > 0 … end` -/
abbrev loopE : Expr := .while' condE bodyE

/-- `class Power … end` -/
abbrev classE : Expr :=
  .class' "Power" none (.seq [
    .def' "initialize" [.req "base"] (.vasgn .ivar "@base" (.var .lvar "base")),
    .def' "raise_to" [.req "exponent"] (.seq [
      .vasgn .lvar "result" (.int 1),
      .vasgn .lvar "square" (.var .ivar "@base"),
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

end Books.FastPower.Fast
