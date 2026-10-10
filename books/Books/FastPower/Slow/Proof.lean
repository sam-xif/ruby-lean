import Books.FastPower.Spec
import Books.FastPower.Slow.Program

/-!
# `slow_power.rb` computes `b ** n`, in `24 * n + 65` transitions

The proof is one inductive invariant over the machine (`Inv`), with two cut
points: the start of the program and the loop test. At the loop test it says
what the loop invariant says, `result * b ^ left = b ^ n`, about the machine's
own frame.
-/
namespace Books.FastPower.Slow
open RubyCore RubyCore.Interp Books
set_option maxRecDepth 1000000

/-! ## The machine at the loop test -/

/-- The machine when control first reaches the loop test. Its heap holds the
    booted core library, class `Power` and one instance; its frame store holds
    the toplevel frame, the class body, `initialize` and `raise_to`. The kernel
    computes all of it. -/
def entry (b : Int) (n : Nat) : Machine := (stepN 47 (start (program b n))).getD default

/-- The machine at the loop test when `result` and `left` hold these values.
    Only `raise_to`'s locals (frame 3) differ from `entry`. -/
def loopHead (b : Int) (n : Nat) (result left : Int) : Machine :=
  let m := entry b n
  let f := m.frames.getD 3 default
  { m with frames := m.frames.set! 3 { f with locals :=
      [("left", .int left), ("result", .int result), ("exponent", .int n)] } }

/-- `left > 0` has been evaluated to `t` and the `while` is about to act on it. -/
def tested (b : Int) (n : Nat) (result left : Int) (t : Bool) : Machine :=
  { loopHead b n result left with ctl := .value (.bool t) }

/-! ## Segments: the straight-line runs between cut points

Each is checked by the kernel executing the model, with every variable left a
variable. -/

/-- Booted, the program defines `Power`, runs `Power.new(b)` and enters
    `raise_to(n)`, arriving at the loop test with `result = 1`, `left = n`. -/
theorem setup (b : Int) (n : Nat) :
    stepN 47 (start (program b n)) = some (loopHead b n 1 n) := by kernel_rfl

/-- Evaluating `left > 0`. -/
theorem test (b : Int) (n : Nat) (r e : Int) :
    stepN 5 (loopHead b n r e) = some (tested b n r e (compare e 0 == .gt)) := by kernel_rfl

/-- The loop body: `result = result * @base; left = left - 1`. -/
theorem body (b : Int) (n : Nat) (r e : Int) :
    stepN 19 (tested b n r e true) = some (loopHead b n (r * b) (e - 1)) := by kernel_rfl

/-- The machine one transition before the program finishes: the loop has
    exited, `raise_to` has returned and `puts` has printed. -/
def final (b : Int) (n : Nat) (r e : Int) : Machine :=
  (stepN 13 (tested b n r e false)).getD default

theorem leave (b : Int) (n : Nat) (r e : Int) :
    stepN 13 (tested b n r e false) = some (final b n r e) := by kernel_rfl

/-- The program's value and final machine. -/
def outcome (b : Int) (n : Nat) (r e : Int) : Value × Machine :=
  match stepFn (final b n r e) with
  | .done v m => (v, m)
  | _ => default

theorem finish (b : Int) (n : Nat) (r e : Int) :
    stepFn (final b n r e) = .done (outcome b n r e).1 (outcome b n r e).2 := by kernel_rfl

theorem outcome_value (b : Int) (n : Nat) (r e : Int) : (outcome b n r e).1 = .int r := by
  kernel_rfl

theorem outcome_out (b : Int) (n : Nat) (r e : Int) :
    (outcome b n r e).2.out = "" ++ (toString r ++ "\n") := by kernel_rfl

/-! ## What the loop test computes -/

theorem gt_zero_test (e : Int) : (compare e 0 == Ordering.gt) = decide (0 < e) := by
  by_cases h : 0 < e
  · simp [h, Int.compare_eq_gt.mpr h]
  · have : compare e 0 ≠ Ordering.gt := fun hc => h (Int.compare_eq_gt.mp hc)
    simp [h, this]

/-- One iteration, from loop test to loop test. -/
theorem iterate (b : Int) (n : Nat) (r : Int) (e : Nat) :
    stepN 24 (loopHead b n r ((e + 1 : Nat) : Int)) = some (loopHead b n (r * b) e) := by
  have h₁ := test b n r ((e + 1 : Nat) : Int)
  rw [gt_zero_test, decide_eq_true (by omega)] at h₁
  have h₂ := body b n r ((e + 1 : Nat) : Int)
  rw [show ((e + 1 : Nat) : Int) - 1 = (e : Int) by omega] at h₂
  exact stepN_add h₁ h₂

/-- Leaving the loop when `left = 0`. -/
theorem exit (b : Int) (n : Nat) (r : Int) :
    stepN 18 (loopHead b n r ((0 : Nat) : Int)) = some (final b n r ((0 : Nat) : Int)) :=
  stepN_add (test b n r ((0 : Nat) : Int)) (leave b n r ((0 : Nat) : Int))

/-! ## The invariant -/

/-- Transitions from the loop test, with `left` iterations to go, to the last
    one before the program finishes: 24 per iteration and 18 to leave. -/
def loopCost (left : Nat) : Nat := 24 * left + 18

/-- Transitions the whole program takes before the one that finishes it. -/
def cost (n : Nat) : Nat := 24 * n + 65

/-- **The invariant.** The machine is at one of the program's two cut points.

    * At the start, with the whole run ahead of it.
    * At the loop test, where `raise_to`'s frame holds a `result` and a `left`
      satisfying the loop invariant `result * b ^ left = b ^ n`, with
      `loopCost left` transitions to go. -/
inductive Inv (b : Int) (n : Nat) : Nat → Machine → Prop
  | start : Inv b n (cost n) (start (program b n))
  | loop (result : Int) (left : Nat) (h : result * b ^ left = b ^ n) :
      Inv b n (loopCost left) (loopHead b n result left)

/-- The invariant is inductive, and when the program finishes from it the
    specification's result holds. -/
theorem inv_inductive (b : Int) (n : Nat) : Inductive (Inv b n) (PowerResult b n) := by
  intro c m hm
  cases hm with
  | start =>
    exact .step 46 (loopCost n) _ (setup b n) (.loop 1 n (Int.one_mul _))
      (by simp only [cost, loopCost]; omega)
  | loop r e h =>
    cases e with
    | zero =>
      rw [Int.pow_zero, Int.mul_one] at h
      refine .finish _ _ _ (exit b n r) (finish b n r _) ⟨?_, ?_⟩
      · rw [outcome_value, h]
      · rw [outcome_out, String.empty_append, h]
    | succ e =>
      refine .step 23 (loopCost e) _ (iterate b n r e) (.loop (r * b) e ?_)
        (by simp only [loopCost]; omega)
      rw [← h, Int.pow_succ, Int.mul_assoc, Int.mul_comm (b ^ e)]

/-- **`slow_power.rb` meets the specification**, and takes exactly `24 * n + 65`
    transitions to do it. -/
theorem computes_power : ComputesPowerIn program cost := fun b n =>
  (inv_inductive b n).returnsIn .start

end Books.FastPower.Slow
