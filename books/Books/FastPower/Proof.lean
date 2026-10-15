import Books.FastPower.Program
import Books.Lib.Boot

/-!
# `fast_power.rb` computes `b ** n`

The theorem is `fast_power_correct` at the bottom. The proof has four parts:

1. **States.** The machine at the loop test, as a function of the values of the
   loop's variables (`loopHead`), and the two places inside an iteration where
   the machine branches on a value that depends on them (`tested`, `parity`).
2. **Segments.** Each straight-line stretch between those states, checked by
   the kernel running `stepFn` (`kernel_rfl`).
3. **Arithmetic.** The loop invariant `result * square ^ left = b ^ n`, which
   is ordinary mathematics about `Int` and has nothing to do with Ruby.
4. **The loop.** Strong induction on `left`, gluing 1–3 together.
-/
namespace Books.FastPower
open RubyCore RubyCore.Interp Books
set_option maxRecDepth 1000000

/-! ## The specification -/

/-- The number of binary digits of `k`: `0` for `0`, otherwise `⌊log₂ k⌋ + 1`.
    This is how many times the loop runs. -/
def bitLength : Nat → Nat
  | 0 => 0
  | k + 1 => bitLength ((k + 1) / 2) + 1
decreasing_by omega

theorem bitLength_zero : bitLength 0 = 0 := by simp [bitLength]

theorem bitLength_pos {k : Nat} (h : 0 < k) : bitLength k = bitLength (k / 2) + 1 := by
  cases k with
  | zero => omega
  | succ k => rw [bitLength]

/-- `bitLength` means what its name says: `2 ^ (bitLength k - 1) ≤ k < 2 ^ bitLength k`. -/
theorem lt_two_pow_bitLength (k : Nat) : k < 2 ^ bitLength k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simp [bitLength_zero]
    | succ k =>
      rw [bitLength_pos (by omega), Nat.pow_succ]
      have := ih ((k + 1) / 2) (by omega)
      omega

theorem two_pow_bitLength_le {k : Nat} (h : 0 < k) : 2 ^ (bitLength k - 1) ≤ k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rw [bitLength_pos h, Nat.add_sub_cancel]
    by_cases h2 : k / 2 = 0
    · rw [h2, bitLength_zero]; simp; omega
    · have ih' := ih (k / 2) (by omega) (by omega)
      have hb := bitLength_pos (k := k / 2) (by omega)
      rw [show bitLength (k / 2) = (bitLength (k / 2) - 1) + 1 by omega, Nat.pow_succ]
      omega

/-! ## 1. States

`#kernel_steps 400 fun (b n : Int) => start (program b n)` reports that the
kernel runs 66 transitions and then cannot decide `left > 0`. Five transitions
earlier the machine is about to evaluate that test for the first time; that is
the loop head. `#eval trace 400 (start (program 3 2))` shows which frame and
which object the loop works on. -/

/-- The machine when control first reaches the loop test, for inputs `b`, `n`.
    Its heap holds the booted core library, class `Power` and one instance; its
    frame store holds the toplevel frame, the class body, `initialize` and
    `raise_to`. None of that is written out here: the kernel computes it. -/
def entry (b n : Int) : Machine := (stepN 61 (start (program b n))).getD default

/-- The machine at the loop test when the loop's variables hold these values.
    Everything the loop does not touch is taken from `entry`; what it does
    touch is spelled out — the locals of `raise_to`'s frame (frame 3) and the
    instance variables of the `Power` object (object 119), whose `revision`
    counts the writes it has received. -/
def loopHead (b n : Int) (result square left : Int) (steps : Nat) : Machine :=
  let m := entry b n
  let f := m.frames.getD 3 default
  let o := m.heap.objs.getD 119 default
  { m with
    frames := m.frames.set! 3 { f with locals :=
      [("left", .int left), ("square", .int square), ("result", .int result),
       ("exponent", .int n)] }
    heap := { m.heap with objs := m.heap.objs.set! 119 { o with
      ivars := [("@steps", .int steps), ("@base", .int b)], revision := steps + 2 } } }

/-- `left > 0` has been evaluated to `t` and the `while` is about to act on it. -/
def tested (b n : Int) (result square left : Int) (steps : Nat) (t : Bool) : Machine :=
  { loopHead b n result square left steps with ctl := .value (.bool t) }

/-- Inside the body: `left % 2 == 1` has been evaluated to `t` and the `if` is
    about to act on it. -/
def parity (b n : Int) (result square left : Int) (steps : Nat) (t : Bool) : Machine :=
  let m := loopHead b n result square left steps
  { m with ctl := .value (.bool t)
           kont := .ifK mulE none :: .seqK [squareE, halveE, tickE] ::
                   .whileBodyK condE bodyE :: m.kont.drop 1 }

/-! ## 2. Segments

Every theorem in this section is proved by the kernel executing the model. The
variables stay variables: these are statements about all inputs. -/

/-- Defining `Power`, `Power.new(b)` (which runs `initialize`), the call to
    `raise_to(n)` and its first three assignments reach the loop head with
    `result = 1`, `square = b`, `left = n`, `@steps = 0`. -/
theorem setup (b n : Int) :
    stepN 61 (start (program b n)) = some (loopHead b n 1 b n 0) := by kernel_rfl

/-- Evaluating `left > 0`. -/
theorem test (b n r s e : Int) (c : Nat) :
    stepN 5 (loopHead b n r s e c) = some (tested b n r s e c (compare e 0 == .gt)) := by
  kernel_rfl

/-- Entering the body and evaluating `left % 2 == 1`. -/
theorem enter (b n r s e : Int) (c : Nat) :
    stepN 12 (tested b n r s e c true) = some (parity b n r s e c (Int.fmod e 2 == 1)) := by
  kernel_rfl

/-- The rest of the body when `left` is odd. -/
theorem odd_iter (b n r s e : Int) (c : Nat) :
    stepN 34 (parity b n r s e c true)
      = some (loopHead b n (r * s) (s * s) (Int.fdiv e 2) (c + 1)) := by
  kernel_rfl

/-- The rest of the body when `left` is even. -/
theorem even_iter (b n r s e : Int) (c : Nat) :
    stepN 27 (parity b n r s e c false)
      = some (loopHead b n r (s * s) (Int.fdiv e 2) (c + 1)) := by
  kernel_rfl

/-- The machine one transition before the program finishes: the loop has
    exited, `raise_to` has returned, `puts` has printed, and the result Array
    has been built. -/
def final (b n r s e : Int) (c : Nat) : Machine :=
  (stepN 21 (tested b n r s e c false)).getD default

theorem leave (b n r s e : Int) (c : Nat) :
    stepN 21 (tested b n r s e c false) = some (final b n r s e c) := by kernel_rfl

/-- The program's value and final machine. -/
def outcome (b n r s e : Int) (c : Nat) : Value × Machine :=
  match stepFn (final b n r s e c) with
  | .done v m => (v, m)
  | _ => default

theorem finish (b n r s e : Int) (c : Nat) :
    stepFn (final b n r s e c) = .done (outcome b n r s e c).1 (outcome b n r s e c).2 := by
  kernel_rfl

theorem outcome_value (b n r s e : Int) (c : Nat) : (outcome b n r s e c).1 = .ref 120 := by
  kernel_rfl

/-- What `puts answer` wrote: the decimal digits of `result` and a newline. -/
theorem outcome_out (b n r s e : Int) (c : Nat) :
    (outcome b n r s e c).2.out = "" ++ (toString r ++ "\n") := by
  kernel_rfl

/-- The value is an Array of the final `result` and `@steps`. -/
theorem outcome_array (b n r s e : Int) (c : Nat) :
    ((outcome b n r s e c).2.heap.get 120).payload = .arr #[.int r, .int c] := by kernel_rfl

/-! ## 3. Arithmetic -/

/-- What `Integer#>` computes against `0`. -/
theorem gt_zero_test (e : Int) : (compare e 0 == Ordering.gt) = decide (0 < e) := by
  by_cases h : 0 < e
  · simp [h, Int.compare_eq_gt.mpr h]
  · have : compare e 0 ≠ Ordering.gt := fun hc => h (Int.compare_eq_gt.mp hc)
    simp [h, this]

/-- What `left % 2 == 1` computes. Ruby's `%` takes the sign of the divisor;
    on a non-negative integer it is the ordinary remainder. -/
theorem odd_test_true {k : Nat} (h : k % 2 = 1) : (Int.fmod ((k : Nat) : Int) 2 == 1) = true := by
  rw [Int.fmod_eq_emod_of_nonneg _ (by decide), show ((k : Nat) : Int) % 2 = 1 by omega]; decide

theorem odd_test_false {k : Nat} (h : k % 2 = 0) :
    (Int.fmod ((k : Nat) : Int) 2 == 1) = false := by
  rw [Int.fmod_eq_emod_of_nonneg _ (by decide), show ((k : Nat) : Int) % 2 = 0 by omega]; decide

/-- Ruby's `/` is floor division; on a non-negative integer that is halving. -/
theorem halve (k : Nat) : Int.fdiv ((k : Nat) : Int) 2 = ((k / 2 : Nat) : Int) :=
  (Int.ofNat_fdiv k 2).symm

theorem sq_pow (s : Int) (m : Nat) : (s * s) ^ m = s ^ (2 * m) := by
  rw [Int.pow_mul]; congr 1
  rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]

/-- The invariant `result * square ^ left` is preserved by an even iteration… -/
theorem pow_even (r s : Int) {k : Nat} (h : k % 2 = 0) : r * (s * s) ^ (k / 2) = r * s ^ k := by
  rw [sq_pow, show 2 * (k / 2) = k by omega]

/-- …and by an odd one. -/
theorem pow_odd (r s : Int) {k : Nat} (h : k % 2 = 1) :
    r * s * (s * s) ^ (k / 2) = r * s ^ k := by
  rw [sq_pow]
  conv => rhs; rw [show k = 2 * (k / 2) + 1 by omega, Int.pow_succ]
  rw [Int.mul_assoc, Int.mul_comm s]

/-! ## 4. The loop

The segments end in tests the kernel left undecided. Here each is resolved from
a hypothesis about `left`, turning segments into `Reaches` facts. -/

theorem test_true {b n r s e : Int} {c : Nat} (h : 0 < e) :
    Reaches (loopHead b n r s e c) (tested b n r s e c true) := by
  have := test b n r s e c
  rw [gt_zero_test, decide_eq_true h] at this
  exact .of_stepN this

theorem test_false {b n r s e : Int} {c : Nat} (h : ¬ 0 < e) :
    Reaches (loopHead b n r s e c) (tested b n r s e c false) := by
  have := test b n r s e c
  rw [gt_zero_test, decide_eq_false h] at this
  exact .of_stepN this

theorem enter_as {b n r s e : Int} {c : Nat} {t : Bool} (h : (Int.fmod e 2 == 1) = t) :
    Reaches (tested b n r s e c true) (parity b n r s e c t) :=
  h ▸ .of_stepN (enter b n r s e c)

theorem odd_step (b n r s : Int) (k c : Nat) :
    Reaches (parity b n r s ((k : Nat) : Int) c true)
      (loopHead b n (r * s) (s * s) ((k / 2 : Nat) : Int) (c + 1)) :=
  halve k ▸ .of_stepN (odd_iter b n r s k c)

theorem even_step (b n r s : Int) (k c : Nat) :
    Reaches (parity b n r s ((k : Nat) : Int) c false)
      (loopHead b n r (s * s) ((k / 2 : Nat) : Int) (c + 1)) :=
  halve k ▸ .of_stepN (even_iter b n r s k c)

/-- **The loop.** Entered with `left = k ≥ 0`, it exits with
    `result * square ^ k` in `result`, having added `bitLength k` to `@steps`. -/
theorem loop (b n : Int) (k : Nat) : ∀ (r s : Int) (c : Nat),
    ∃ s' e', Reaches (loopHead b n r s k c)
      (tested b n (r * s ^ k) s' e' (c + bitLength k) false) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro r s c
    by_cases hk : k = 0
    · subst hk
      refine ⟨s, ((0 : Nat) : Int), ?_⟩
      rw [Int.pow_zero, Int.mul_one, bitLength_zero]
      exact test_false (by decide)
    · have hlt : k / 2 < k := by omega
      have hpos : (0 : Int) < ((k : Nat) : Int) := by omega
      have hbits : c + bitLength k = c + 1 + bitLength (k / 2) := by
        rw [bitLength_pos (by omega : 0 < k)]; omega
      rw [hbits]
      by_cases hodd : k % 2 = 1
      · obtain ⟨s', e', h⟩ := ih _ hlt (r * s) (s * s) (c + 1)
        refine ⟨s', e', ?_⟩
        rw [← pow_odd r s hodd]
        exact (test_true hpos).trans <| (enter_as (odd_test_true hodd)).trans <|
          (odd_step b n r s k c).trans h
      · have heven : k % 2 = 0 := by omega
        obtain ⟨s', e', h⟩ := ih _ hlt r (s * s) (c + 1)
        refine ⟨s', e', ?_⟩
        rw [← pow_even r s heven]
        exact (test_true hpos).trans <| (enter_as (odd_test_false heven)).trans <|
          (even_step b n r s k c).trans h

/-- The loop from any `left`, including a negative one, where it does not run. -/
theorem loop_any (b n e r s : Int) (c : Nat) :
    ∃ s' e', Reaches (loopHead b n r s e c)
      (tested b n (r * s ^ e.toNat) s' e' (c + bitLength e.toNat) false) := by
  by_cases he : 0 ≤ e
  · have := loop b n e.toNat r s c
    rwa [Int.toNat_of_nonneg he] at this
  · have h0 : e.toNat = 0 := by omega
    have hneg : ¬ 0 < e := by omega
    refine ⟨s, e, ?_⟩
    rw [h0, Int.pow_zero, Int.mul_one, bitLength_zero]
    exact test_false hneg

/-! ## The theorem -/

/-- **`fast_power.rb` is correct.** Run the way `rubycore` runs it, for every
    base `b` and exponent `n`, the program terminates normally, prints `b ** n`
    on a line of its own, and its value is the Array `[b ** n, s]`, where `s`,
    the number of loop iterations, is the bit length of `n`. A negative exponent
    behaves as `0`. -/
theorem fast_power_correct (b n : Int) :
    ∃ v m', Runs (program b n) v m' ∧
      m'.out = toString (b ^ n.toNat) ++ "\n" ∧
      IsArray m'.heap v [.int (b ^ n.toNat), .int (bitLength n.toNat)] := by
  obtain ⟨s', e', hloop⟩ := loop_any b n n 1 b 0
  rw [Int.one_mul, Nat.zero_add] at hloop
  let r := b ^ n.toNat
  let c := bitLength n.toNat
  refine ⟨(outcome b n r s' e' c).1, (outcome b n r s' e' c).2, ⟨_, boot_ok _, ?_⟩, ?_,
    120, outcome_value b n r s' e' c, outcome_array b n r s' e' c⟩
  · exact .of_reaches
      ((Reaches.of_stepN (setup b n)).trans <| hloop.trans (.of_stepN (leave b n r s' e' c)))
      (finish b n r s' e' c)
  · rw [outcome_out, String.empty_append]

/-- The same, read as a statement about the interpreter at any fuel: the run
    is either still going, or it has returned the right answer. It never
    raises, never leaves the modeled fragment, and never gets stuck. -/
theorem fast_power_run (b n : Int) (fuel : Nat) :
    ∃ m₀, Prelude.initWithPrelude (program b n) = .ok m₀ ∧
      ((∃ m, run fuel m₀ = .outOfFuel m) ∨
       ∃ v m, run fuel m₀ = .value v m ∧ m.out = toString (b ^ n.toNat) ++ "\n" ∧
         IsArray m.heap v [.int (b ^ n.toNat), .int (bitLength n.toNat)]) := by
  obtain ⟨v, m', ⟨m₀, hboot, hret⟩, hout, harr⟩ := fast_power_correct b n
  refine ⟨m₀, hboot, ?_⟩
  rcases hret.run_eq fuel with h | h
  · exact .inr ⟨v, m', h, hout, harr⟩
  · exact .inl h

end Books.FastPower
