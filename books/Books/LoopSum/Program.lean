import RubyCore.Interp

/-! `loop_sum.rb` as a RubyCore term, with the loop bound abstracted:
`program n` is the program with `while x < n`. `Check.lean` fails the build if
`program 100` stops being what the desugarer exports for `loop_sum.rb`. -/
namespace Books.LoopSum
open RubyCore

/-- `x < n` -/
abbrev condE (n : Int) : Expr := .send (some (.var .lvar "x")) "<" [.int n] none
/-- `y += x`, the statement at `HERE` -/
abbrev addE : Expr :=
  .vasgn .lvar "y" (.send (some (.var .lvar "y")) "+" [.var .lvar "x"] none)
/-- `x += 1` -/
abbrev incE : Expr :=
  .vasgn .lvar "x" (.send (some (.var .lvar "x")) "+" [.int 1] none)
/-- The loop body. -/
abbrev bodyE : Expr := .seq [addE, incE]

/-- The whole program, for loop bound `n`. -/
def program (n : Int) : Expr :=
  .seq [
    .vasgn .lvar "x" (.int 0),
    .vasgn .lvar "y" (.int 0),
    .while' (condE n) bodyE,
    .send none "puts" [.var .lvar "y"] none,
    .var .lvar "y"]

end Books.LoopSum
