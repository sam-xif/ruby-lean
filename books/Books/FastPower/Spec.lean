import Books.Lib.Invariant

/-!
# The specification: a program that computes `b ** n`

Nothing here mentions a loop, a class or a machine state. A program meets the
specification by what it prints and returns.
-/
namespace Books.FastPower
open RubyCore

/-- What a run for base `b` and exponent `n` must end with: the value `b ** n`,
    and `b ** n` printed on a line of its own. -/
def PowerResult (b : Int) (n : Nat) (v : Value) (m' : Machine) : Prop :=
  v = .int (b ^ n) ∧ m'.out = toString (b ^ n) ++ "\n"

/-- **The specification.** `program b n` is a Ruby program for each base `b` and
    exponent `n`. Run the way `rubycore` runs it, it terminates normally, prints
    `b ** n` and has the value `b ** n`. -/
def ComputesPower (program : Int → Nat → Expr) : Prop :=
  ∀ (b : Int) (n : Nat), ∃ v m', Runs (program b n) v m' ∧ PowerResult b n v m'

/-- The specification with a running time: for exponent `n` the run takes
    exactly `cost n` transitions before the one that finishes it. -/
def ComputesPowerIn (program : Int → Nat → Expr) (cost : Nat → Nat) : Prop :=
  ∀ (b : Int) (n : Nat), ∃ v m', RunsIn (program b n) (cost n) v m' ∧ PowerResult b n v m'

theorem ComputesPowerIn.computesPower {program : Int → Nat → Expr} {cost : Nat → Nat}
    (h : ComputesPowerIn program cost) : ComputesPower program := fun b n =>
  let ⟨v, m', hrun, hres⟩ := h b n; ⟨v, m', hrun.runs, hres⟩

/-- The running time is a property of the program, not of the proof: a program
    has only one. -/
theorem ComputesPowerIn.cost_unique {program : Int → Nat → Expr} {cost : Nat → Nat}
    (h : ComputesPowerIn program cost) {b : Int} {n k : Nat} {v : Value} {m' : Machine}
    (hk : RunsIn (program b n) k v m') : k = cost n :=
  let ⟨_, _, hrun, _⟩ := h b n; (hk.unique hrun).1

end Books.FastPower
