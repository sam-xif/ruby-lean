import Books.FastPower.Spec
import Books.FastPower.Fast.Program

/-!
# `fast_power.rb` computes `b ** n`, in about `43 * log₂ n` transitions

The proof is one inductive invariant over the machine (`Inv`), with two cut
points: the start of the program and the loop test. At the loop test it says
what the loop invariant says, `result * square ^ left = b ^ n`, about the
machine's own frame.

An iteration has two paths, for `left` odd and `left` even, so the running time
depends on the binary digits of `n`. `loopCost` is that time exactly, and
`cost_le`/`le_cost` bound it by the number of digits.
-/
namespace Books.FastPower.Fast
open RubyCore RubyCore.Interp Books
set_option maxRecDepth 1000000

/-! ## The machine at the loop test -/

/-- The machine when control first reaches the loop test. Its heap holds the
    booted core library, class `Power` and one instance; its frame store holds
    the toplevel frame, the class body, `initialize` and `raise_to`. The kernel
    computes all of it. -/
def entry (b : Int) (n : Nat) : Machine := (stepN 51 (start (program b n))).getD default

/-- The machine at the loop test when `result`, `square` and `left` hold these
    values. Only `raise_to`'s locals (frame 3) differ from `entry`. -/
def loopHead (b : Int) (n : Nat) (result square left : Int) : Machine :=
  let m := entry b n
  let f := m.frames.getD 3 default
  { m with frames := m.frames.set! 3 { f with locals :=
      [("left", .int left), ("square", .int square), ("result", .int result),
       ("exponent", .int n)] } }

/-- `left > 0` has been evaluated to `t` and the `while` is about to act on it. -/
def tested (b : Int) (n : Nat) (result square left : Int) (t : Bool) : Machine :=
  { loopHead b n result square left with ctl := .value (.bool t) }

/-- Inside the body: `left % 2 == 1` has been evaluated to `t` and the `if` is
    about to act on it. -/
def parity (b : Int) (n : Nat) (result square left : Int) (t : Bool) : Machine :=
  let m := loopHead b n result square left
  { m with ctl := .value (.bool t)
           kont := .ifK mulE none :: .seqK [squareE, halveE] ::
                   .whileBodyK condE bodyE :: m.kont.drop 1 }

/-! ## Segments: the straight-line runs between cut points

Each is checked by the kernel executing the model, with every variable left a
variable. -/

/-- Booted, the program defines `Power`, runs `Power.new(b)` and enters
    `raise_to(n)`, arriving at the loop test with `result = 1`, `square = b`,
    `left = n`. -/
theorem setup (b : Int) (n : Nat) :
    stepN 51 (start (program b n)) = some (loopHead b n 1 b n) := by kernel_rfl

/-- Evaluating `left > 0`. -/
theorem test (b : Int) (n : Nat) (r s e : Int) :
    stepN 5 (loopHead b n r s e) = some (tested b n r s e (compare e 0 == .gt)) := by
  kernel_rfl

/-- Entering the body and evaluating `left % 2 == 1`. -/
theorem enter (b : Int) (n : Nat) (r s e : Int) :
    stepN 12 (tested b n r s e true) = some (parity b n r s e (Int.fmod e 2 == 1)) := by
  kernel_rfl

/-- The rest of the body when `left` is odd. -/
theorem odd_body (b : Int) (n : Nat) (r s e : Int) :
    stepN 26 (parity b n r s e true) = some (loopHead b n (r * s) (s * s) (Int.fdiv e 2)) := by
  kernel_rfl

/-- The rest of the body when `left` is even. -/
theorem even_body (b : Int) (n : Nat) (r s e : Int) :
    stepN 19 (parity b n r s e false) = some (loopHead b n r (s * s) (Int.fdiv e 2)) := by
  kernel_rfl

/-- The machine one transition before the program finishes: the loop has
    exited, `raise_to` has returned and `puts` has printed. -/
def final (b : Int) (n : Nat) (r s e : Int) : Machine :=
  (stepN 13 (tested b n r s e false)).getD default

theorem leave (b : Int) (n : Nat) (r s e : Int) :
    stepN 13 (tested b n r s e false) = some (final b n r s e) := by kernel_rfl

/-- The program's value and final machine. -/
def outcome (b : Int) (n : Nat) (r s e : Int) : Value × Machine :=
  match stepFn (final b n r s e) with
  | .done v m => (v, m)
  | _ => default

theorem finish (b : Int) (n : Nat) (r s e : Int) :
    stepFn (final b n r s e) = .done (outcome b n r s e).1 (outcome b n r s e).2 := by
  kernel_rfl

theorem outcome_value (b : Int) (n : Nat) (r s e : Int) :
    (outcome b n r s e).1 = .int r := by kernel_rfl

theorem outcome_out (b : Int) (n : Nat) (r s e : Int) :
    (outcome b n r s e).2.out = "" ++ (toString r ++ "\n") := by kernel_rfl

/-! ## What the tests and the arithmetic compute -/

theorem gt_zero_test (e : Int) : (compare e 0 == Ordering.gt) = decide (0 < e) := by
  by_cases h : 0 < e
  · simp [h, Int.compare_eq_gt.mpr h]
  · have : compare e 0 ≠ Ordering.gt := fun hc => h (Int.compare_eq_gt.mp hc)
    simp [h, this]

/-- `left % 2 == 1`. Ruby's `%` takes the sign of the divisor; on a
    non-negative integer it is the ordinary remainder. -/
theorem odd_test (k : Nat) : (Int.fmod ((k : Nat) : Int) 2 == 1) = decide (k % 2 = 1) := by
  rw [Int.fmod_eq_emod_of_nonneg _ (by decide)]
  by_cases h : k % 2 = 1
  · rw [show ((k : Nat) : Int) % 2 = 1 by omega, decide_eq_true h]; decide
  · rw [show ((k : Nat) : Int) % 2 = 0 by omega, decide_eq_false h]; decide

/-- Ruby's `/` is floor division; on a non-negative integer that is halving. -/
theorem halve (k : Nat) : Int.fdiv ((k : Nat) : Int) 2 = ((k / 2 : Nat) : Int) :=
  (Int.ofNat_fdiv k 2).symm

theorem sq_pow (s : Int) (m : Nat) : (s * s) ^ m = s ^ (2 * m) := by
  rw [Int.pow_mul]; congr 1
  rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]

/-- The loop invariant `result * square ^ left` is preserved by an even
    iteration… -/
theorem pow_even (r s : Int) {k : Nat} (h : k % 2 = 0) : r * (s * s) ^ (k / 2) = r * s ^ k := by
  rw [sq_pow, show 2 * (k / 2) = k by omega]

/-- …and by an odd one. -/
theorem pow_odd (r s : Int) {k : Nat} (h : k % 2 = 1) :
    r * s * (s * s) ^ (k / 2) = r * s ^ k := by
  rw [sq_pow]
  conv => rhs; rw [show k = 2 * (k / 2) + 1 by omega, Int.pow_succ]
  rw [Int.mul_assoc, Int.mul_comm s]

/-! ## Paths between cut points -/

/-- One iteration with `left` odd, from loop test to loop test. -/
theorem iterate_odd (b : Int) (n : Nat) (r s : Int) {k : Nat} (hk : k % 2 = 1) :
    stepN 43 (loopHead b n r s k) = some (loopHead b n (r * s) (s * s) ((k / 2 : Nat) : Int)) := by
  have hpos : (0 : Int) < ((k : Nat) : Int) := by omega
  have h₁ := test b n r s k
  rw [gt_zero_test, decide_eq_true hpos] at h₁
  have h₂ := enter b n r s k
  rw [odd_test, decide_eq_true hk] at h₂
  have h₃ := odd_body b n r s k
  rw [halve] at h₃
  exact stepN_add (stepN_add h₁ h₂) h₃

/-- One iteration with `left` even and positive. -/
theorem iterate_even (b : Int) (n : Nat) (r s : Int) {k : Nat} (hpos : 0 < k) (hk : k % 2 = 0) :
    stepN 36 (loopHead b n r s k) = some (loopHead b n r (s * s) ((k / 2 : Nat) : Int)) := by
  have hpos' : (0 : Int) < ((k : Nat) : Int) := by omega
  have hk' : ¬ k % 2 = 1 := by omega
  have h₁ := test b n r s k
  rw [gt_zero_test, decide_eq_true hpos'] at h₁
  have h₂ := enter b n r s k
  rw [odd_test, decide_eq_false hk'] at h₂
  have h₃ := even_body b n r s k
  rw [halve] at h₃
  exact stepN_add (stepN_add h₁ h₂) h₃

/-- Leaving the loop when `left = 0`. -/
theorem exit (b : Int) (n : Nat) (r s : Int) :
    stepN 18 (loopHead b n r s ((0 : Nat) : Int)) = some (final b n r s ((0 : Nat) : Int)) :=
  stepN_add (test b n r s ((0 : Nat) : Int)) (leave b n r s ((0 : Nat) : Int))

/-! ## The invariant -/

/-- Transitions from the loop test, with `left` still to process, to the last
    one before the program finishes: 43 for an odd `left`, 36 for an even one,
    then the same for `left / 2`; 18 to leave. -/
def loopCost : Nat → Nat
  | 0 => 18
  | k + 1 => (if (k + 1) % 2 = 1 then 43 else 36) + loopCost ((k + 1) / 2)
decreasing_by omega

theorem loopCost_zero : loopCost 0 = 18 := by simp [loopCost]

theorem loopCost_pos {k : Nat} (h : 0 < k) :
    loopCost k = (if k % 2 = 1 then 43 else 36) + loopCost (k / 2) := by
  cases k with
  | zero => omega
  | succ k => rw [loopCost]

/-- Transitions the whole program takes before the one that finishes it. -/
def cost (n : Nat) : Nat := 51 + loopCost n

/-- **The invariant.** The machine is at one of the program's two cut points.

    * At the start, with the whole run ahead of it.
    * At the loop test, where `raise_to`'s frame holds a `result`, a `square`
      and a `left` satisfying the loop invariant
      `result * square ^ left = b ^ n`, with `loopCost left` transitions to go. -/
inductive Inv (b : Int) (n : Nat) : Nat → Machine → Prop
  | start : Inv b n (cost n) (start (program b n))
  | loop (result square : Int) (left : Nat) (h : result * square ^ left = b ^ n) :
      Inv b n (loopCost left) (loopHead b n result square left)

/-- The invariant is inductive, and when the program finishes from it the
    specification's result holds. -/
theorem inv_inductive (b : Int) (n : Nat) : Inductive (Inv b n) (PowerResult b n) := by
  intro c m hm
  cases hm with
  | start => exact .step 50 (loopCost n) _ (setup b n) (.loop 1 b n (Int.one_mul _)) rfl
  | loop r s k h =>
    by_cases hk : k = 0
    · subst hk
      rw [Int.pow_zero, Int.mul_one] at h
      rw [loopCost_zero]
      refine .finish _ _ _ (exit b n r s) (finish b n r s _) ⟨?_, ?_⟩
      · rw [outcome_value, h]
      · rw [outcome_out, String.empty_append, h]
    · have hpos : 0 < k := by omega
      rw [loopCost_pos hpos]
      by_cases hodd : k % 2 = 1
      · exact .step 42 (loopCost (k / 2)) _ (iterate_odd b n r s hodd)
          (.loop _ _ _ (by rw [pow_odd r s hodd, h])) (by rw [if_pos hodd])
      · have heven : k % 2 = 0 := by omega
        exact .step 35 (loopCost (k / 2)) _ (iterate_even b n r s hpos heven)
          (.loop _ _ _ (by rw [pow_even r s heven, h])) (by rw [if_neg hodd])

/-- **`fast_power.rb` meets the specification**, and takes exactly `cost n`
    transitions to do it. -/
theorem computes_power : ComputesPowerIn program cost := fun b n =>
  (inv_inductive b n).returnsIn .start

end Books.FastPower.Fast
