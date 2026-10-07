import RubyCore.Interp

/-! `ruby/fast_power.rb` as a RubyCore term, with its two integer literals
abstracted: `program b n` is the program that computes `b ** n`. -/
namespace Books.FastPower
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
/-- `@steps = @steps + 1` -/
abbrev tickE : Expr :=
  .vasgn .ivar "@steps" (.send (some (.var .ivar "@steps")) "+" [.int 1] none)
/-- The loop body. -/
abbrev bodyE : Expr := .seq [.if' oddE mulE none, squareE, halveE, tickE]
/-- `while left > 0 … end` -/
abbrev loopE : Expr := .while' condE bodyE

/-- `class Power … end` -/
abbrev classE : Expr :=
  .class' "Power" none (.seq [
    .def' "initialize" [.req "base"] (.seq [
      .vasgn .ivar "@base" (.var .lvar "base"),
      .vasgn .ivar "@steps" (.int 0)]),
    .def' "steps" [] (.var .ivar "@steps"),
    .def' "raise_to" [.req "exponent"] (.seq [
      .vasgn .lvar "result" (.int 1),
      .vasgn .lvar "square" (.var .ivar "@base"),
      .vasgn .lvar "left" (.var .lvar "exponent"),
      loopE,
      .var .lvar "result"])])

/-- The whole program, for base `b` and exponent `n`. -/
def program (b n : Int) : Expr :=
  .seq [
    classE,
    .vasgn .lvar "power" (.send (some (.const "Power")) "new" [.int b] none),
    .vasgn .lvar "answer" (.send (some (.var .lvar "power")) "raise_to" [.int n] none),
    .send none "puts" [.var .lvar "answer"] none,
    .array [.var .lvar "answer", .send (some (.var .lvar "power")) "steps" [] none]]

end Books.FastPower
