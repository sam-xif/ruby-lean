import Books.FastPower.Slow.Proof
import Books.FastPower.Fast.Proof

/-!
# Both programs meet the specification, and the fast one is faster

Running time here is the number of machine transitions. A transition that
multiplies two integers counts as one however large they are, so this measures
how many operations each program performs, not how long the arithmetic takes. It
does not depend on the base at all.

* `slow_power.rb` takes `24 * n + 65` transitions.
* `fast_power.rb` takes between `36 * bitLength n + 69` and
  `43 * bitLength n + 69`, where `bitLength n` is the number of binary digits
  of `n`: logarithmic in the exponent.
* From `n = 6` on the fast program takes strictly fewer; up to `n = 5` the slow
  one does.
-/
namespace Books.FastPower
open RubyCore Books

/-! ## The specification holds of both -/

theorem slow_computes_power : ComputesPower Slow.program :=
  Slow.computes_power.computesPower

theorem fast_computes_power : ComputesPower Fast.program :=
  Fast.computes_power.computesPower

/-! ## The number of binary digits -/

/-- The number of binary digits of `k`: `0` for `0`, otherwise `⌊log₂ k⌋ + 1`. -/
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

/-! ## The fast program's running time is logarithmic -/

theorem loopCost_le (k : Nat) : Fast.loopCost k ≤ 43 * bitLength k + 18 := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k = 0
    · subst hk; rw [Fast.loopCost_zero, bitLength_zero]; omega
    · have := ih (k / 2) (by omega)
      rw [Fast.loopCost_pos (by omega), bitLength_pos (by omega)]
      split <;> omega

theorem le_loopCost (k : Nat) : 36 * bitLength k + 18 ≤ Fast.loopCost k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k = 0
    · subst hk; rw [Fast.loopCost_zero, bitLength_zero]; omega
    · have := ih (k / 2) (by omega)
      rw [Fast.loopCost_pos (by omega), bitLength_pos (by omega)]
      split <;> omega

/-- At most 43 transitions per binary digit of the exponent… -/
theorem fast_cost_le (n : Nat) : Fast.cost n ≤ 43 * bitLength n + 69 := by
  have := loopCost_le n; simp only [Fast.cost]; omega

/-- …and at least 36. -/
theorem le_fast_cost (n : Nat) : 36 * bitLength n + 69 ≤ Fast.cost n := by
  have := le_loopCost n; simp only [Fast.cost]; omega

/-! ## The comparison -/

/-- From 6 on, 43 transitions per binary digit are fewer than 24 per unit. -/
theorem digits_lt_linear (k : Nat) (h : 6 ≤ k) : 43 * bitLength k + 4 < 24 * k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h12 : 12 ≤ k
    · have := ih (k / 2) (by omega) (by omega)
      rw [bitLength_pos (by omega)]; omega
    · have h3 : bitLength 3 = 2 := by
        rw [bitLength_pos (by omega), bitLength_pos (by omega), bitLength_zero]
      have h5 : bitLength 5 = 3 := by
        rw [bitLength_pos (by omega), bitLength_pos (by omega), bitLength_pos (by omega),
          bitLength_zero]
      have h4 : bitLength 4 = 3 := by
        rw [bitLength_pos (by omega), bitLength_pos (by omega), bitLength_pos (by omega),
          bitLength_zero]
      have hk : bitLength k = bitLength (k / 2) + 1 := bitLength_pos (by omega)
      have : k / 2 = 3 ∨ k / 2 = 4 ∨ k / 2 = 5 := by omega
      rcases this with e | e | e <;> rw [e] at hk <;> omega

/-- For every exponent from 6 up, the fast program's running time is strictly
    smaller than the slow program's. -/
theorem fast_cost_lt_slow_cost (n : Nat) (h : 6 ≤ n) : Fast.cost n < Slow.cost n := by
  have h₁ := fast_cost_le n
  have h₂ := digits_lt_linear n h
  simp only [Slow.cost]; omega

/-- **The fast program is faster.** For any base and any exponent from 6 up,
    however many transitions each program's run takes, the fast program's run
    takes fewer. -/
theorem fast_is_faster (b : Int) (n : Nat) (h : 6 ≤ n)
    {slow fast : Nat} {v v' : Value} {m m' : Machine}
    (hs : RunsIn (Slow.program b n) slow v m) (hf : RunsIn (Fast.program b n) fast v' m') :
    fast < slow := by
  rw [Slow.computes_power.cost_unique hs, Fast.computes_power.cost_unique hf]
  exact fast_cost_lt_slow_cost n h

/-- The threshold is exact: up to 5 the slow program takes fewer transitions,
    because it does less work per iteration. -/
theorem slow_cost_lt_fast_cost (n : Nat) (h : n ≤ 5) : Slow.cost n < Fast.cost n := by
  have h0 := Fast.loopCost_zero
  have h1 : Fast.loopCost 1 = 61 := by rw [Fast.loopCost_pos (by omega), h0]; rfl
  have h2 : Fast.loopCost 2 = 97 := by rw [Fast.loopCost_pos (by omega), h1]; rfl
  have h3 : Fast.loopCost 3 = 104 := by rw [Fast.loopCost_pos (by omega), h1]; rfl
  have h4 : Fast.loopCost 4 = 133 := by rw [Fast.loopCost_pos (by omega), h2]; rfl
  have h5 : Fast.loopCost 5 = 140 := by rw [Fast.loopCost_pos (by omega), h2]; rfl
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  simp only [Slow.cost, Fast.cost]
  rcases this with e | e | e | e | e | e <;> subst e <;> omega

end Books.FastPower
