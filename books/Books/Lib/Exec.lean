import Lean
import RubyCore.Interp

/-!
# Kernel-checked symbolic execution of the RubyCore machine

`stepFn` is a total, executable function, and the Lean kernel can evaluate it —
including method dispatch — on a machine whose integer inputs are *variables*.
Everything here is built on that one fact.

* `stepN k m` runs `k` ordinary transitions.
* `Reaches m m'` says some number of transitions takes `m` to `m'`.
* `kernel_rfl` proves `stepN k m = some m'` for a straight-line stretch of
  execution by asking the kernel to run it.

A straight-line stretch ends where the machine would branch on a value the
kernel cannot decide (`left > 0` for a variable `left`). There the proof takes
over: it rewrites the undecided test using a hypothesis, and execution resumes.
-/
namespace Books
open RubyCore RubyCore.Interp

/-- `k` ordinary (`.next`) transitions; `none` if the machine finishes, raises
    or gates before that. -/
def stepN : Nat → Machine → Option Machine
  | 0, m => some m
  | k + 1, m =>
    match stepFn m with
    | .next m' => stepN k m'
    | _ => none

theorem stepN_add {j k : Nat} {m m₁ m₂ : Machine}
    (h₁ : stepN j m = some m₁) (h₂ : stepN k m₁ = some m₂) :
    stepN (j + k) m = some m₂ := by
  induction j generalizing m with
  | zero => simp only [stepN, Option.some.injEq] at h₁; subst h₁; simpa using h₂
  | succ j ih =>
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only [stepN] at h₁ ⊢
    split at h₁
    · exact ih h₁
    · exact absurd h₁ (by simp)

/-- `m` reaches `m'` in finitely many ordinary transitions. -/
def Reaches (m m' : Machine) : Prop := ∃ k, stepN k m = some m'

theorem Reaches.refl (m : Machine) : Reaches m m := ⟨0, rfl⟩

theorem Reaches.trans {a b c : Machine} (h₁ : Reaches a b) (h₂ : Reaches b c) :
    Reaches a c :=
  let ⟨_, e₁⟩ := h₁; let ⟨_, e₂⟩ := h₂; ⟨_, stepN_add e₁ e₂⟩

theorem Reaches.of_stepN {k : Nat} {m m' : Machine} (h : stepN k m = some m') :
    Reaches m m' := ⟨k, h⟩

instance : Trans Reaches Reaches Reaches := ⟨Reaches.trans⟩

/-- The program started in `m` terminates normally with value `v`, leaving the
    machine in state `m'`. No exception, no unsupported construct, no stuck
    state — `run` distinguishes all of those from `.value`. -/
def Returns (m : Machine) (v : Value) (m' : Machine) : Prop :=
  ∃ fuel, run fuel m = .value v m'

theorem run_of_stepN {k : Nat} {m m₁ : Machine} (h : stepN k m = some m₁) (fuel : Nat) :
    run (k + fuel) m = run fuel m₁ := by
  induction k generalizing m with
  | zero => simp only [stepN, Option.some.injEq] at h; subst h; simp
  | succ k ih =>
    rw [show k + 1 + fuel = (k + fuel) + 1 by omega]
    simp only [stepN] at h
    simp only [run]
    split at h
    · rename_i m' hs; rw [hs]; exact ih h
    · exact absurd h (by simp)

theorem Returns.of_reaches {m m₁ m' : Machine} {v : Value}
    (h : Reaches m m₁) (hd : stepFn m₁ = .done v m') : Returns m v m' := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rw [run_of_stepN hk 1]; simp [run, hd]⟩

/-- A terminating program has one outcome, whatever the fuel: with too little
    the run is still going, and with enough it returns exactly `v` and `m'`.
    In particular no amount of fuel makes it raise, gate or get stuck. -/
theorem Returns.run_eq {m m' : Machine} {v : Value} (h : Returns m v m') (fuel : Nat) :
    run fuel m = .value v m' ∨ ∃ m'', run fuel m = .outOfFuel m'' := by
  obtain ⟨f₀, h₀⟩ := h
  induction fuel generalizing m f₀ with
  | zero => exact .inr ⟨m, rfl⟩
  | succ fuel ih =>
    cases f₀ with
    | zero => simp [run] at h₀
    | succ f₀ =>
      simp only [run] at h₀ ⊢
      split <;> rename_i hs <;> rw [hs] at h₀ <;> simp_all
      exact ih _ h₀

open Lean Elab Tactic Meta in
/-- Close `a = b` with `Eq.refl a` and leave the check to the kernel, which
    evaluates `stepFn` far faster than the elaborator and is not stopped by the
    irreducibility of well-founded definitions such as `invoke`. If the two
    sides are not definitionally equal the *declaration* is rejected. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, a, _) := t.eq? | throwError "kernel_rfl: the goal is not an equality"
  g.assign (← mkEqRefl a)

end Books

namespace Books
open Lean Elab Command Meta RubyCore RubyCore.Interp

/-- `#kernel_steps k m`: run up to `k` transitions from `m` with the kernel and
    say where the kernel first cannot decide the next one. `m` may be a function
    (`fun (b n : Int) => …`), whose arguments are then left symbolic. This is how
    the end of a straight-line stretch is found. -/
elab "#kernel_steps " k:num m:term : command => liftTermElabM do
  let m ← Term.elabTerm m none
  Term.synthesizeSyntheticMVarsNoPostponing
  let m ← instantiateMVars m
  lambdaTelescope m fun _ body => do
    let env ← getEnv
    let lctx ← getLCtx
    -- One kernel call per probe, so that the kernel's cache covers the whole run.
    let runs (j : Nat) : MetaM Bool := do
      let r ← ofExceptKernelException
        (Kernel.whnf env lctx (mkApp2 (mkConst ``stepN) (mkNatLit j) body))
      return r.isAppOfArity ``Option.some 2
    if ← runs k.getNat then
      logInfo m!"ran {k.getNat} transitions"
      return
    -- the largest `j` for which `stepN j m` still runs
    let mut lo := 0
    let mut hi := k.getNat
    while lo + 1 < hi do
      let mid := (lo + hi) / 2
      if ← runs mid then lo := mid else hi := mid
    let reached ← mkAppM ``Option.getD
      #[mkApp2 (mkConst ``stepN) (mkNatLit lo) body, ← mkAppOptM ``default #[mkConst ``Machine, none]]
    let r ← ofExceptKernelException (Kernel.whnf env lctx (mkApp (mkConst ``stepFn) reached))
    logInfo m!"stopped after {lo} transitions; the next one reduces to:\n{(toString (← ppExpr r)).take 3000}"

/-- `#kernel_whnf e`: the kernel's weak-head normal form of `e`. -/
elab "#kernel_whnf " e:term : command => liftTermElabM do
  let e ← Term.elabTerm e none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  lambdaTelescope e fun _ body => do
    let r ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) body)
    logInfo m!"{(toString (← ppExpr r)).take 3000}"

end Books

