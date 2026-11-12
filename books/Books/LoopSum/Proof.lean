import Books.Lib.Boot
import Books.LoopSum.Program

/-!
# A loop invariant of `loop_sum.rb`

```ruby
x = 0
y = 0
while x < 100
  # HERE
  y += x
  x += 1
end
puts y
y
```

The theorem is `invariant`: every time control reaches `HERE`, `y` is the sum
of the integers in `0...x` (upper bound exclusive). It is stated about every
state of the run, not only the ones the proof builds: if the machine is ever
about to evaluate `y += x`, the invariant holds there. `here_visited` says that
`HERE` is in fact reached, once for each `x` in `0...100`, and
`loop_sum_correct` that the program then prints and returns the sum of
`0...100`.

The loop bound is a variable `n` throughout (`program n`), so the results hold
for every bound, `100` included.

The proof has five parts:

1. **States.** The machine at the loop test, at `HERE`, and after the test, as
   functions of `x` and `y`.
2. **Segments.** The straight-line stretches between them, checked by the
   kernel running `stepFn`.
3. **Every visit.** Each segment, also checked by the kernel, passes no state at
   `HERE` except where it starts. Since the machine is deterministic, the states
   the segments join are the only ones at `HERE`.
4. **Arithmetic.** What `x < n` and `+` compute, and `sumBelow (x + 1) =
   sumBelow x + x`.
5. **The loop.** Induction on the number of iterations left.
-/
namespace Books.LoopSum
open RubyCore RubyCore.Interp Books
set_option maxRecDepth 1000000

/-! ## The specification -/

/-- The sum of the integers in `0...x`. -/
def sumBelow (x : Nat) : Int := ((List.range x).sum : Nat)

theorem sumBelow_zero : sumBelow 0 = 0 := rfl

theorem sumBelow_succ (x : Nat) : sumBelow (x + 1) = sumBelow x + x := by
  simp [sumBelow, List.range_succ, List.sum_append]

/-- The closed form, as a check that `sumBelow` is the intended sum. -/
theorem two_mul_sumBelow (x : Nat) : 2 * sumBelow x = x * (x - 1 : Int) := by
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [sumBelow_succ, Int.mul_add, ih]
    push_cast
    rw [Int.add_sub_cancel, Int.mul_sub, Int.mul_one, Int.add_mul, Int.one_mul]
    omega

/-- The machine is at `HERE`: about to evaluate `y += x` (`addE`), the first
    statement of the loop body. The statement occurs once in the program, so
    this is exactly the program point the comment marks. It is a pattern match
    rather than `== addE` because the kernel cannot evaluate the derived `BEq`
    on `Expr`. -/
def atHere (m : Machine) : Bool :=
  match m.ctl with
  | .eval (.vasgn .lvar "y" (.send (some (.var .lvar "y")) "+" [.var .lvar "x"] none)) => true
  | _ => false

theorem atHere_addE (m : Machine) (h : m.ctl = .eval addE) : atHere m = true := by
  simp [atHere, h]

/-- The value of local variable `name` in the running frame. -/
def localVar (m : Machine) (name : String) : Option Value :=
  match m.stack with
  | f :: _ => (m.frames.getD f default).locals.lookup name
  | [] => none

/-- **The invariant**, for loop bound `n`: `x` holds an integer in `0...n`
    and `y` holds the sum of the integers below it. -/
def Invariant (n : Int) (m : Machine) : Prop :=
  ∃ x : Nat, (x : Int) < n ∧
    localVar m "x" = some (.int x) ∧ localVar m "y" = some (.int (sumBelow x))

/-! ## 1. States

`#kernel_steps 400 fun (n : Int) => start (program n)` reports that the kernel
runs 15 transitions and then cannot decide `x < n`. Five transitions earlier
control is about to evaluate that test for the first time; that is the loop
head. `#eval trace 60 (start (program 2))` (from `Books.Lib.Trace`) shows the
run: the program never leaves the toplevel frame, and `+` and `<` on integers
are builtins that push no frame. -/

/-- The machine when control first reaches the loop test: the booted heap, one
    frame, `x = 0`, `y = 0`. The kernel computes it. -/
def entry (n : Int) : Machine := (stepN 10 (start (program n))).getD default

/-- The toplevel frame's locals. An assignment moves the variable to the front,
    so before the first iteration (`first`) `y` comes first and afterwards `x`
    does. -/
def locs (first : Bool) (x y : Int) : List (String × Value) :=
  if first then [("y", .int y), ("x", .int x)] else [("x", .int x), ("y", .int y)]

/-- The machine at the loop test, with `x` and `y` holding these values.
    Everything else is taken from `entry`. -/
def loopHead (first : Bool) (n x y : Int) : Machine :=
  let m := entry n
  let f := m.frames.getD 0 default
  { m with frames := m.frames.set! 0 { f with locals := locs first x y } }

/-- `x < n` has been evaluated to `t` and the `while` is about to act on it. -/
def tested (first : Bool) (n x y : Int) (t : Bool) : Machine :=
  { loopHead first n x y with ctl := .value (.bool t) }

/-- The machine at `HERE`. -/
def here (first : Bool) (n x y : Int) : Machine :=
  let m := loopHead first n x y
  { m with ctl := .eval addE
           kont := .seqK [incE] :: .whileBodyK (condE n) bodyE :: m.kont.drop 1 }

/-! ## 2. Segments

Each theorem here is proved by the kernel executing the model, for all values
of the variables. -/

/-- `x = 0` and `y = 0`. -/
theorem setup (n : Int) : stepN 10 (start (program n)) = some (loopHead true n 0 0) := by
  kernel_rfl

/-- Evaluating `x < n`. -/
theorem test (f : Bool) (n x y : Int) :
    stepN 5 (loopHead f n x y) = some (tested f n x y (compare x n == .lt)) := by
  cases f <;> kernel_rfl

/-- Entering the body. -/
theorem enter (f : Bool) (n x y : Int) :
    stepN 2 (tested f n x y true) = some (here f n x y) := by
  cases f <;> kernel_rfl

/-- `y += x` and `x += 1`, back to the test. -/
theorem body (f : Bool) (n x y : Int) :
    stepN 17 (here f n x y) = some (loopHead false n (x + 1) (y + x)) := by
  cases f <;> kernel_rfl

/-- The machine one transition before the program finishes: the loop has
    exited and `puts y` has printed. -/
def final (f : Bool) (n x y : Int) : Machine := (stepN 8 (tested f n x y false)).getD default

theorem leave (f : Bool) (n x y : Int) :
    stepN 8 (tested f n x y false) = some (final f n x y) := by
  cases f <;> kernel_rfl

/-- The program's value and final machine. -/
def outcome (f : Bool) (n x y : Int) : Value × Machine :=
  match stepFn (final f n x y) with
  | .done v m => (v, m)
  | _ => default

theorem finish (f : Bool) (n x y : Int) :
    stepFn (final f n x y) = .done (outcome f n x y).1 (outcome f n x y).2 := by
  cases f <;> kernel_rfl

/-- The program's value is `y`. -/
theorem outcome_value (f : Bool) (n x y : Int) : (outcome f n x y).1 = .int y := by
  cases f <;> kernel_rfl

/-- What `puts y` wrote. -/
theorem outcome_out (f : Bool) (n x y : Int) :
    (outcome f n x y).2.out = "" ++ (toString y ++ "\n") := by
  cases f <;> kernel_rfl

/-- What `x` and `y` hold at `HERE`. -/
theorem here_x (f : Bool) (n x y : Int) : localVar (here f n x y) "x" = some (.int x) := by
  cases f <;> kernel_rfl

theorem here_y (f : Bool) (n x y : Int) : localVar (here f n x y) "y" = some (.int y) := by
  cases f <;> kernel_rfl

/-! ## 3. Every visit to `HERE`

`clearFor c m` runs `c` transitions from `m` and says that none of the states
it passes, the last included, is at `HERE`. The kernel evaluates it on each
segment. With the determinism of `stepN` that is enough to know every state of
the run at `HERE`. -/

/-- None of the `c` states after `m` is at `HERE`. -/
def clearFor : Nat → Machine → Bool
  | 0, _ => true
  | c + 1, m =>
    match stepFn m with
    | .next m' => !atHere m' && clearFor c m'
    | _ => true

theorem clearFor_spec {c k : Nat} {a m : Machine} (h : clearFor c a = true)
    (hk₀ : 0 < k) (hk : k ≤ c) (hm : stepN k a = some m) : atHere m = false := by
  induction c generalizing a k with
  | zero => omega
  | succ c ih =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [clearFor] at h
    simp only [stepN] at hm
    split at hm
    · rename_i a' hs
      rw [hs] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      by_cases hk0 : k = 0
      · subst hk0; simp only [stepN, Option.some.injEq] at hm; exact hm ▸ h.1
      · exact ih h.2 (by omega) (by omega) hm
    · exact absurd hm (by simp)

/-- `stepN` is a function: a run that passes `b` after `j` transitions
    continues from `b`. -/
theorem stepN_sub {j k : Nat} {a b : Machine} (h : stepN j a = some b) (hjk : j ≤ k) :
    stepN k a = stepN (k - j) b := by
  induction j generalizing a k with
  | zero => simp only [stepN, Option.some.injEq] at h; subst h; rfl
  | succ j ih =>
    obtain ⟨k, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    simp only [stepN] at h ⊢
    split at h
    · rw [show k + 1 - (j + 1) = k - j by omega]; exact ih h (by omega)
    · exact absurd h (by simp)

/-- Every state reachable from `m` that is at `HERE` satisfies `P`. -/
def AtHereAlways (P : Machine → Prop) (m : Machine) : Prop :=
  ∀ k m', stepN k m = some m' → atHere m' = true → P m'

/-- A segment from `a` to `b` that passes `HERE` at most where it starts. -/
theorem AtHereAlways.segment {P : Machine → Prop} {L : Nat} {a b : Machine}
    (hab : stepN (L + 1) a = some b) (hc : clearFor L a = true)
    (ha : atHere a = true → P a) (hb : AtHereAlways P b) : AtHereAlways P a := by
  intro k m hk hm
  by_cases k0 : k = 0
  · subst k0; simp only [stepN, Option.some.injEq] at hk; subst hk; exact ha hm
  by_cases kL : k ≤ L
  · exact absurd (clearFor_spec hc (by omega) kL hk) (by simp [hm])
  · rw [stepN_sub hab (by omega)] at hk; exact hb _ _ hk hm

/-- A machine that finishes in one transition reaches nothing else. -/
theorem AtHereAlways.done {P : Machine → Prop} {a : Machine} {v : Value} {m : Machine}
    (hd : stepFn a = .done v m) (ha : atHere a = false) : AtHereAlways P a := by
  intro k m' hk hm
  cases k with
  | zero => simp only [stepN, Option.some.injEq] at hk; subst hk; simp [ha] at hm
  | succ k => simp [stepN, hd] at hk

theorem setup_clear (n : Int) : clearFor 9 (start (program n)) = true := by kernel_rfl
theorem start_not_here (n : Int) : atHere (start (program n)) = false := by kernel_rfl
theorem test_clear (f : Bool) (n x y : Int) : clearFor 4 (loopHead f n x y) = true := by
  cases f <;> kernel_rfl
theorem loopHead_not_here (f : Bool) (n x y : Int) : atHere (loopHead f n x y) = false := by
  cases f <;> kernel_rfl
theorem tested_not_here (f : Bool) (n x y : Int) (t : Bool) :
    atHere (tested f n x y t) = false := by
  cases f <;> kernel_rfl
theorem enter_clear (f : Bool) (n x y : Int) : clearFor 1 (tested f n x y true) = true := by
  cases f <;> kernel_rfl
theorem body_clear (f : Bool) (n x y : Int) : clearFor 16 (here f n x y) = true := by
  cases f <;> kernel_rfl
theorem leave_clear (f : Bool) (n x y : Int) : clearFor 7 (tested f n x y false) = true := by
  cases f <;> kernel_rfl
theorem final_not_here (f : Bool) (n x y : Int) : atHere (final f n x y) = false := by
  cases f <;> kernel_rfl

/-! ## 4. Arithmetic -/

/-- What `Integer#<` computes. -/
theorem lt_test (x n : Int) : (compare x n == Ordering.lt) = decide (x < n) := by
  by_cases h : x < n
  · simp [h, Int.compare_eq_lt.mpr h]
  · have : compare x n ≠ Ordering.lt := fun hc => h (Int.compare_eq_lt.mp hc)
    simp [h, this]

theorem succ_cast (x : Nat) : ((x : Nat) : Int) + 1 = ((x + 1 : Nat) : Int) := by omega

theorem sum_step (x : Nat) : sumBelow x + ((x : Nat) : Int) = sumBelow (x + 1) :=
  (sumBelow_succ x).symm

/-! ## 5. The loop -/

theorem test_true {f : Bool} {n x y : Int} (h : x < n) :
    stepN 5 (loopHead f n x y) = some (tested f n x y true) := by
  have := test f n x y; rwa [lt_test, decide_eq_true h] at this

theorem test_false {f : Bool} {n x y : Int} (h : ¬ x < n) :
    stepN 5 (loopHead f n x y) = some (tested f n x y false) := by
  have := test f n x y; rwa [lt_test, decide_eq_false h] at this

/-- One iteration from the loop test, with `y` the sum below `x`. -/
theorem iter (f : Bool) (n : Int) (x : Nat) :
    stepN 17 (here f n x (sumBelow x)) = some (loopHead false n (x + 1 : Nat) (sumBelow (x + 1))) :=
  succ_cast x ▸ sum_step x ▸ body f n x (sumBelow x)

/-- The invariant holds at the `HERE` state the proof builds. -/
theorem here_invariant (f : Bool) {n : Int} {x : Nat} (h : (x : Int) < n) :
    Invariant n (here f n x (sumBelow x)) :=
  ⟨x, h, here_x .., here_y ..⟩

/-- From the loop test, every visit to `HERE` satisfies the invariant. By
    induction on the iterations left, `n - x`. -/
theorem loop_always (n : Int) (d : Nat) : ∀ (f : Bool) (x : Nat), (n - x).toNat = d →
    AtHereAlways (Invariant n) (loopHead f n x (sumBelow x)) := by
  induction d with
  | zero =>
    intro f x hd
    have hx : ¬ (x : Int) < n := by omega
    refine .segment (L := 4) (test_false hx) (test_clear ..) (by simp [loopHead_not_here]) ?_
    refine .segment (L := 7) (leave f n x _) (leave_clear ..) (by simp [tested_not_here]) ?_
    exact .done (finish ..) (final_not_here ..)
  | succ d ih =>
    intro f x hd
    have hx : (x : Int) < n := by omega
    have hrest := ih false (x + 1) (by omega)
    refine .segment (L := 4) (test_true hx) (test_clear ..) (by simp [loopHead_not_here]) ?_
    refine .segment (L := 1) (enter ..) (enter_clear ..) (by simp [tested_not_here]) ?_
    exact .segment (L := 16) (iter f n x) (body_clear ..) (fun _ => here_invariant f hx) hrest

/-- **The loop invariant.** For every loop bound `n`, every state of the run of
    `program n` that is at `HERE`, about to evaluate `y += x`, has `x` in
    `0...n` and `y` equal to the sum of the integers in `0...x`. -/
theorem invariant (n : Int) (k : Nat) (m : Machine)
    (hk : stepN k (start (program n)) = some m) (hm : atHere m = true) :
    Invariant n m := by
  have hloop := loop_always n _ true 0 rfl
  rw [sumBelow_zero] at hloop
  exact (AtHereAlways.segment (L := 9) (setup n) (setup_clear n)
    (by simp [start_not_here]) hloop) k m hk hm

/-- The same, for `loop_sum.rb` itself. -/
theorem loop_sum_invariant (k : Nat) (m : Machine)
    (hk : stepN k (start (program 100)) = some m) (hm : atHere m = true) :
    ∃ x : Nat, x < 100 ∧
      localVar m "x" = some (.int x) ∧ localVar m "y" = some (.int (sumBelow x)) := by
  obtain ⟨x, hx, h⟩ := invariant 100 k m hk hm
  exact ⟨x, by omega, h⟩

/-! ## `HERE` is reached, and the program finishes

The invariant would hold trivially of a program that never reached `HERE`.
These say it does, once for each `x` in `0...n`, and then terminates. -/

/-- From the loop test with `x`, the test with `x + i`, if every iteration
    in between runs. -/
theorem heads (n : Int) (i : Nat) : ∀ (f : Bool) (x : Nat), ((x + i : Nat) : Int) ≤ n →
    ∃ f', Reaches (loopHead f n x (sumBelow x)) (loopHead f' n (x + i : Nat) (sumBelow (x + i))) := by
  induction i with
  | zero => intro f x _; exact ⟨f, .refl _⟩
  | succ i ih =>
    intro f x hx
    obtain ⟨f', h⟩ := ih false (x + 1) (by omega)
    refine ⟨f', ?_⟩
    rw [show x + (i + 1) = x + 1 + i by omega]
    exact (Reaches.of_stepN (test_true (by omega))).trans <|
      (Reaches.of_stepN (enter ..)).trans <| (Reaches.of_stepN (iter f n x)).trans h

/-- The states named `here` are at `HERE`. -/
theorem here_at (f : Bool) (n x y : Int) : atHere (here f n x y) = true := atHere_addE _ rfl

/-- **`HERE` is visited** with each `x` in `0...n`, `y` holding the sum below it. -/
theorem here_visited (n : Int) (x : Nat) (hx : (x : Int) < n) :
    ∃ m, Reaches (start (program n)) m ∧ atHere m = true ∧
      localVar m "x" = some (.int x) ∧ localVar m "y" = some (.int (sumBelow x)) := by
  obtain ⟨f, h⟩ := heads n x true 0 (by omega)
  rw [Nat.zero_add, show ((0 : Nat) : Int) = 0 from rfl, sumBelow_zero] at h
  exact ⟨_, (Reaches.of_stepN (setup n)).trans <| h.trans <|
    (Reaches.of_stepN (test_true hx)).trans (.of_stepN (enter ..)),
    here_at .., here_x .., here_y ..⟩

/-- **`loop_sum.rb` terminates**, for every bound `n`, prints the sum of
    `0...n` on a line of its own, and returns it. -/
theorem loop_sum_correct (n : Int) :
    ∃ m', Runs (program n) (.int (sumBelow n.toNat)) m' ∧
      m'.out = toString (sumBelow n.toNat) ++ "\n" := by
  obtain ⟨f, h⟩ : ∃ f, Reaches (loopHead true n 0 0)
      (loopHead f n (n.toNat : Nat) (sumBelow n.toNat)) := by
    by_cases hn : 0 ≤ n
    · obtain ⟨f, h⟩ := heads n n.toNat true 0 (by omega)
      rw [Nat.zero_add, show ((0 : Nat) : Int) = 0 from rfl, sumBelow_zero] at h
      exact ⟨f, h⟩
    · rw [show n.toNat = 0 by omega]; exact ⟨true, .refl _⟩
  have hexit : ¬ ((n.toNat : Nat) : Int) < n := by omega
  let y := sumBelow n.toNat
  refine ⟨(outcome f n n.toNat y).2, ⟨_, boot_ok _, ?_⟩, ?_⟩
  · rw [← outcome_value f n n.toNat y]
    exact .of_reaches ((Reaches.of_stepN (setup n)).trans <| h.trans <|
      (Reaches.of_stepN (test_false hexit)).trans (.of_stepN (leave ..))) (finish ..)
  · rw [outcome_out, String.empty_append]

/-- `loop_sum.rb` prints and returns `4950`. -/
theorem loop_sum_100 :
    ∃ m', Runs (program 100) (.int 4950) m' ∧ m'.out = "4950\n" :=
  loop_sum_correct 100

end Books.LoopSum
