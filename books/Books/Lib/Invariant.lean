import Books.Lib.Boot

/-!
# Inductive invariants at cut points

The way a loop is proved correct here is the inductive-assertion method, stated
directly over the machine.

Choose the *cut points* of the program: its start, and the head of each loop.
An invariant `Inv c m` says "`m` is at a cut point, the program's variables
satisfy the loop invariant there, and exactly `c` more transitions finish the
program". It is *inductive* if every machine it holds of either

* runs, in at least one transition, to another machine it holds of, with the
  count reduced by exactly that many transitions; or
* finishes, in exactly `c` transitions, with a value and a final machine that
  satisfy the postcondition.

`Inductive.returnsIn` is the theorem that pays for this: from any machine an
inductive invariant holds of, the program terminates normally, in exactly `c`
transitions, and the postcondition holds. The count is what makes the argument
well founded — each advance spends at least one transition — so one number
serves as both the termination measure and the running time.

Between cut points the machine runs in a straight line, which the kernel checks
by evaluation (`kernel_rfl`). So proving an invariant inductive takes one
segment per path between cut points, and the arithmetic showing the loop
invariant is re-established.
-/
namespace Books
open RubyCore RubyCore.Interp

/-- `m` terminates normally after exactly `k` ordinary transitions and the one
    that finishes, with value `v`, leaving the machine in state `m'`. -/
def ReturnsIn (m : Machine) (k : Nat) (v : Value) (m' : Machine) : Prop :=
  ∃ m₁, stepN k m = some m₁ ∧ stepFn m₁ = .done v m'

theorem ReturnsIn.returns {m m' : Machine} {k : Nat} {v : Value}
    (h : ReturnsIn m k v m') : Returns m v m' :=
  let ⟨_, hk, hd⟩ := h; .of_reaches (.of_stepN hk) hd

/-- A machine has one running time and one outcome. -/
theorem ReturnsIn.unique {m m₁ m₂ : Machine} {j k : Nat} {v w : Value}
    (h₁ : ReturnsIn m j v m₁) (h₂ : ReturnsIn m k w m₂) : j = k ∧ v = w ∧ m₁ = m₂ := by
  obtain ⟨a, ha, hda⟩ := h₁
  obtain ⟨b, hb, hdb⟩ := h₂
  induction j generalizing m k with
  | zero =>
    simp only [stepN, Option.some.injEq] at ha; subst ha
    cases k with
    | zero =>
      simp only [stepN, Option.some.injEq] at hb; subst hb
      rw [hda] at hdb; injection hdb with hv hm; exact ⟨rfl, hv, hm⟩
    | succ k => simp [stepN, hda] at hb
  | succ j ih =>
    cases k with
    | zero =>
      simp only [stepN, Option.some.injEq] at hb; subst hb
      simp [stepN, hdb] at ha
    | succ k =>
      simp only [stepN] at ha hb
      split at ha
      · rename_i m' hs
        rw [hs] at hb
        obtain ⟨hjk, hv, hm⟩ := ih ha hb
        exact ⟨by omega, hv, hm⟩
      · exact absurd ha (by simp)

/-- One advance from a cut point: on to another cut point, or to the end. -/
inductive Advance (Inv : Nat → Machine → Prop) (Post : Value → Machine → Prop)
    (c : Nat) (m : Machine) : Prop
  /-- `k + 1` transitions reach a machine the invariant holds of, with `c'` to go. -/
  | step (k c' : Nat) (m' : Machine) (run : stepN (k + 1) m = some m') (inv : Inv c' m')
      (count : c = k + 1 + c')
  /-- `c` transitions and the finishing one end the program in a state the
      postcondition accepts. -/
  | finish (m₁ : Machine) (v : Value) (m' : Machine) (run : stepN c m = some m₁)
      (done : stepFn m₁ = .done v m') (post : Post v m')

/-- The invariant is preserved by the program: every machine it holds of
    advances. -/
def Inductive (Inv : Nat → Machine → Prop) (Post : Value → Machine → Prop) : Prop :=
  ∀ c m, Inv c m → Advance Inv Post c m

/-- **An inductive invariant proves total correctness and the running time.**
    From a machine it holds of with count `c`, the program terminates normally
    in exactly `c` transitions, in a state the postcondition accepts. -/
theorem Inductive.returnsIn {Inv : Nat → Machine → Prop} {Post : Value → Machine → Prop}
    (h : Inductive Inv Post) {c : Nat} {m : Machine} (hm : Inv c m) :
    ∃ v m', ReturnsIn m c v m' ∧ Post v m' := by
  induction c using Nat.strongRecOn generalizing m with
  | ind c ih =>
    cases h c m hm with
    | step k c' m' run inv count =>
      obtain ⟨v, mf, ⟨m₁, hk, hd⟩, hpost⟩ := ih c' (by omega) inv
      exact ⟨v, mf, ⟨m₁, count ▸ stepN_add run hk, hd⟩, hpost⟩
    | finish m₁ v m' run done post => exact ⟨v, m', ⟨m₁, run, done⟩, post⟩

/-- `program`, run the way `rubycore` runs it, terminates normally after exactly
    `k` transitions with value `v`, leaving the machine in state `m'`. -/
def RunsIn (program : Expr) (k : Nat) (v : Value) (m' : Machine) : Prop :=
  ReturnsIn (start program) k v m'

theorem RunsIn.runs {program : Expr} {k : Nat} {v : Value} {m' : Machine}
    (h : RunsIn program k v m') : Runs program v m' :=
  ⟨_, boot_ok program, h.returns⟩

end Books
