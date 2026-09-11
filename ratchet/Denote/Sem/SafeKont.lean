import Denote.Sem.Answer

/-!
# `Denote/Sem/SafeKont.lean` — the continuation obligation, answer-indexed

**Design**: `../../../docs/semantics/answer-typed-judgments.md` §6, second bullet — "`SafeKont
K` becomes indexed by `Answer`. The escape case is a *clause* rather than a missing
hypothesis, and it can carry `StateOk` — which is precisely what made `JumpStuckFree` false."

This file is that, plus the fuel arithmetic a back edge needs.

## What `SafeKont` is

`SafeKont K P Q` reads: *whenever the sub-computation hands `K` an answer satisfying `P`, the
rest of the run satisfies `Q`.* `P` is a predicate on `Answer × Machine`, so writing it down
forces a clause per arm — the `val` clause is the rule's typing content, the `esc` clause is
its control content, and neither can be silently omitted, which is what §2.1 measured
happening under `Evals`.

`Q` is left abstract because the two axes differ only in it: `Q r := typeStuck r = false` is
stuck-freedom, `Q r := ∀ v m', r = .value v m' → …` is value typing. The composition theorem
is proved once.

## The two facts about `Q` a composition needs

`HaltBlind` and the `outOfFuel` clause. Both are trivial for every `Q` this ladder uses and
both are *stated* because they are the price of `Interp.run`'s two machine-reporting
irregularities (`Answer.lean` §Why `Halt` carries the machine). A `Q` that read the machine
out of an `.unsupported` would not compose, and the hypothesis says so out loud.

## What this replaces

`JumpOpaque` (`Decompose.lean`) and `JumpStuckFree` (`VasgnStuck.lean`) are both gone. They
were the same idea — "`K` does not do anything interesting with an escape" — stated once per
axis and, at a loop, **false**. Under `SafeKont` a continuation that *does* do something
interesting with an escape (re-enter the loop) is not a counterexample, it is a case, and the
case is discharged from the `esc` clause of `P`.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## Fuel arithmetic

Two facts about `runA` and one about `Interp.run`, all of them the sort of thing that is
obvious until a back edge needs it in writing. -/

/-- A run that has landed stays landed. `Interp.run`'s own docstring asserts this in passing
("a run that has landed on `.value` stays there"); a loop needs it as a theorem, because the
escape hypothesis arrives at one fuel and is spent at another. -/
def isOofR : Interp.RunResult → Bool
  | .outOfFuel _ => true
  | _ => false

theorem run_succ_eq : ∀ (f : Nat) (m : Machine), isOofR (Interp.run f m) = false →
    Interp.run (f + 1) m = Interp.run f m := by
  intro f
  induction f with
  | zero => intro m h; exact absurd h (by simp [run_zero, isOofR])
  | succ n ih =>
    intro m h
    rw [run_succ n m] at h
    rw [run_succ (n + 1) m, run_succ n m]
    cases hev : Interp.stepFn m with
    | next m' => simp only [hev] at h ⊢; exact ih m' h
    | done v m' => rfl
    | uncaught exc m' => rfl
    | unsupported r => rfl
    | stuck msg => rfl

theorem run_le_eq : ∀ (d f : Nat) (m : Machine), isOofR (Interp.run f m) = false →
    Interp.run (f + d) m = Interp.run f m := by
  intro d
  induction d with
  | zero => intro f m _; rfl
  | succ n ih =>
    intro f m h
    have hn : Interp.run (f + n) m = Interp.run f m := ih f m h
    have hne : isOofR (Interp.run (f + n) m) = false := by rw [hn]; exact h
    calc Interp.run (f + (n + 1)) m = Interp.run ((f + n) + 1) m := by rw [Nat.add_assoc]
      _ = Interp.run (f + n) m := run_succ_eq (f + n) m hne
      _ = Interp.run f m := hn

/-- More fuel finds the same answer, later. The answer point is determined by the machine, so
the only thing extra fuel changes is the remainder. -/
theorem runA_add : ∀ (fuel : Nat) (m : Machine) (a : Answer) (m₀ : Machine) (rest : Nat),
    runA fuel m = .ans a m₀ rest → ∀ d, runA (fuel + d) m = .ans a m₀ (rest + d) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m a m₀ rest h d
    cases hap : answerPoint m with
    | some a' =>
      rw [runA_ans hap] at h ⊢
      injection h with h1 h2 h3
      subst h1; subst h2; subst h3; simp
    | none => rw [runA_zero hap] at h; exact absurd h (by simp)
  | succ n ih =>
    intro m a m₀ rest h d
    cases hap : answerPoint m with
    | some a' =>
      rw [runA_ans hap] at h
      injection h with h1 h2 h3
      subst h1; subst h2; subst h3
      rw [runA_ans hap]
    | none =>
      rw [runA_succ hap] at h
      have hstep : n + 1 + d = (n + d) + 1 := by omega
      rw [hstep, runA_succ hap]
      cases hev : Interp.stepFn m with
      | next m' => simp only [hev] at h ⊢; exact ih m' a m₀ rest h d
      | done v m' =>
        rw [hev] at h
        -- `.done` is only ever at an answer point (`done_inv`), and this is not one
        exfalso
        obtain ⟨hc, hk, -⟩ := RubyCore.Proof.done_inv m v m' hev
        rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap; simp at hap
      | uncaught exc m' => rw [hev] at h; exact absurd h (by simp)
      | unsupported r => rw [hev] at h; exact absurd h (by simp)
      | stuck msg => rw [hev] at h; exact absurd h (by simp)

/-- The remainder is a remainder. What a back edge spends: the next iteration runs on strictly
less fuel than the loop was entered with, and *that* is what makes the loop's induction
well-founded rather than any syntactic measure. -/
theorem runA_rest_le : ∀ (fuel : Nat) (m : Machine) (a : Answer) (m₀ : Machine) (rest : Nat),
    runA fuel m = .ans a m₀ rest → rest ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro m a m₀ rest h
    cases hap : answerPoint m with
    | some a' => rw [runA_ans hap] at h; injection h with h1 h2 h3; omega
    | none => rw [runA_zero hap] at h; exact absurd h (by simp)
  | succ n ih =>
    intro m a m₀ rest h
    cases hap : answerPoint m with
    | some a' => rw [runA_ans hap] at h; injection h with h1 h2 h3; omega
    | none =>
      rw [runA_succ hap] at h
      cases hev : Interp.stepFn m with
      | next m' => simp only [hev] at h; exact Nat.le_succ_of_le (ih m' a m₀ rest h)
      | done v m' =>
        exfalso
        obtain ⟨hc, hk, -⟩ := RubyCore.Proof.done_inv m v m' hev
        rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap; simp at hap
      | uncaught exc m' => rw [hev] at h; exact absurd h (by simp)
      | unsupported r => rw [hev] at h; exact absurd h (by simp)
      | stuck msg => rw [hev] at h; exact absurd h (by simp)

/-- The answer point is where the answer was found. Needed wherever a caller has to know
that the machine it received is one the *inner* run also stops at — which is what makes a
premise about the sub-run consumable. -/
theorem answerPoint_of_ans : ∀ (fuel : Nat) (m : Machine) (a : Answer) (m₀ : Machine)
    (rest : Nat), runA fuel m = .ans a m₀ rest → answerPoint m₀ = some a := by
  intro fuel
  induction fuel with
  | zero =>
    intro m a m₀ rest h
    cases hap : answerPoint m with
    | some a' =>
      rw [runA_ans hap] at h; injection h with h1 h2 h3
      subst h1; subst h2; exact hap
    | none => rw [runA_zero hap] at h; exact absurd h (by simp)
  | succ n ih =>
    intro m a m₀ rest h
    cases hap : answerPoint m with
    | some a' =>
      rw [runA_ans hap] at h; injection h with h1 h2 h3
      subst h1; subst h2; exact hap
    | none =>
      rw [runA_succ hap] at h
      cases hev : Interp.stepFn m with
      | next m' => simp only [hev] at h; exact ih m' a m₀ rest h
      | done v m' =>
        exfalso
        obtain ⟨hc, hk, -⟩ := RubyCore.Proof.done_inv m v m' hev
        rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap; simp at hap
      | uncaught exc m' => rw [hev] at h; exact absurd h (by simp)
      | unsupported r => rw [hev] at h; exact absurd h (by simp)
      | stuck msg => rw [hev] at h; exact absurd h (by simp)

/-- At an answer point the delivery to the *empty* continuation is the machine itself: an
answer point already has an empty continuation and the answer already in flight. -/
theorem deliverA_nil_self {m₀ : Machine} {a : Answer} (h : answerPoint m₀ = some a) :
    deliverA a m₀ [] = m₀ := by
  cases hk : m₀.kont with
  | cons k r => rw [answerPoint, hk] at h; simp at h
  | nil =>
    cases hc : m₀.ctl with
    | eval e => rw [answerPoint, hk] at h; simp only at h; rw [hc] at h; simp at h
    | value v =>
      rw [answerPoint, hk] at h; simp only at h; rw [hc] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [deliverA, Answer.ctl, ← hc, ← hk]
    | jump j =>
      rw [answerPoint, hk] at h; simp only at h; rw [hc] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [deliverA, Answer.ctl, ← hc, ← hk]

/-! ## The continuation obligation -/

/-- **What a continuation owes.** Delivering any `P`-answer to `K` leaves a `Q` run. -/
def SafeKont (K : List Kont) (P : Answer → Machine → Prop)
    (Q : Interp.RunResult → Prop) : Prop :=
  ∀ (a : Answer) (m₀ : Machine), P a m₀ → ∀ f, Q (Interp.run f (deliverA a m₀ K))

/-- **What a sub-computation guarantees.** Every answer it can hand back satisfies `P` — one
clause per `Answer` arm, which is the point of the exercise. -/
def Delivers (m : Machine) (P : Answer → Machine → Prop) : Prop :=
  ∀ (fuel : Nat) (a : Answer) (m₀ : Machine) (rest : Nat), runA fuel m = .ans a m₀ rest →
    P a m₀

/-- `Q` does not read the continuation off a halt's reported machine. -/
def HaltBlind (Q : Interp.RunResult → Prop) : Prop :=
  ∀ (h : Halt) (K K' : List Kont), Q (h.out K) → Q (h.out K')

/-- **Composition, all fuel.** The `vasgn` shape: a continuation that is consumed rather than
re-entered. -/
theorem safe_pushK {K : List Kont} {P : Answer → Machine → Prop}
    {Q : Interp.RunResult → Prop} (hK : RubyCore.Proof.CatchFree K) (hb : HaltBlind Q)
    (hoof : ∀ m₀, Q (.outOfFuel m₀)) {m : Machine}
    (hin : ∀ f, Q (Interp.run f m)) (hP : Delivers m P) (hsafe : SafeKont K P Q) :
    ∀ fuel, Q (Interp.run fuel (pushK K m)) := by
  intro fuel
  rw [run_pushK K hK fuel m]
  cases hr : runA fuel m with
  | ans a m₀ rest => exact hsafe a m₀ (hP fuel a m₀ rest hr) rest
  | halt h =>
    have := hin fuel
    rw [run_eq_out_nil fuel m, hr] at this
    exact hb h [] K this
  | oof m₀ => exact hoof _

/-- **Composition, bounded.** The same theorem with the fuel left at the answer point exposed
— which is what a back edge needs, and the only reason `VasgnStuck.lean` has two versions of
its decomposition. Here the bound is not a second induction: `runA_rest_le` is a fact about
`runA`, proved once, and the statement just passes it on. -/
theorem safe_pushK_le {K : List Kont} {P : Answer → Machine → Prop}
    {Q : Interp.RunResult → Prop} (hK : RubyCore.Proof.CatchFree K) (hb : HaltBlind Q)
    (hoof : ∀ m₀, Q (.outOfFuel m₀)) {m : Machine} {N : Nat}
    (hin : ∀ f, Q (Interp.run f m)) (hP : Delivers m P)
    (hsafe : ∀ (a : Answer) (m₀ : Machine) (rest : Nat), P a m₀ → rest ≤ N →
      Q (Interp.run rest (deliverA a m₀ K))) :
    ∀ fuel, fuel ≤ N → Q (Interp.run fuel (pushK K m)) := by
  intro fuel hfuel
  rw [run_pushK K hK fuel m]
  cases hr : runA fuel m with
  | ans a m₀ rest =>
    exact hsafe a m₀ rest (hP fuel a m₀ rest hr)
      (Nat.le_trans (runA_rest_le fuel m a m₀ rest hr) hfuel)
  | halt h =>
    have := hin fuel
    rw [run_eq_out_nil fuel m, hr] at this
    exact hb h [] K this
  | oof m₀ => exact hoof _

/-! ## The stuck-freedom axis, as one instance

`Q := typeStuck · = false`. Both of the composition theorem's `Q` hypotheses are two-line
computations, which is the evidence that they are bookkeeping rather than content. -/

/-- Stuck-freedom of a *machine*, so that the premise a rule receives and the premise a
continuation discharges are the same predicate. `StuckFree m e` is this at `evalFrom m e`. -/
def SafeA (m : Machine) : Prop :=
  ∀ fuel, Semantics.typeStuck (Interp.run fuel m) = false

theorem stuckFree_iff_safeA (m : Machine) (e : Ratchet.Expr) :
    StuckFree m e ↔ SafeA (evalFrom m e) := Iff.rfl

/-- `typeStuck` reads `.uncaught` and nothing else, and `.uncaught` is the one halt arm whose
machine `Halt.out` does not touch. -/
theorem haltBlind_stuck : HaltBlind (fun r => Semantics.typeStuck r = false) := by
  intro h K K' hq
  cases h <;> simp only [Halt.out, Semantics.typeStuck] at hq ⊢ <;> exact hq

theorem oof_stuck : ∀ m₀, Semantics.typeStuck (.outOfFuel m₀) = false := by
  intro _; rfl

/-- **Every answer a stuck-free computation delivers is stuck-free to carry on with.**

The lemma that makes the `esc` clause payable, and the only place the fuel arithmetic is
spent. Read at the `esc` arm it says: if evaluating `e` never gets stuck, then neither does
the escape it leaves in flight, *unwound at the empty continuation* — which is exactly the
fact `JumpStuckFree` was trying to be a hypothesis about, now a consequence of the premise
the rule already has. -/
theorem delivers_safeA {m : Machine} (h : SafeA m) :
    Delivers m (fun a m₀ => SafeA (deliverA a m₀ [])) := by
  intro fuel a m₀ rest hr f
  by_cases hoof : isOofR (Interp.run f (deliverA a m₀ [])) = true
  · -- out of fuel is not a type error
    cases hcase : Interp.run f (deliverA a m₀ []) with
    | outOfFuel _ => simp [Semantics.typeStuck]
    | value _ _ => rw [hcase] at hoof; exact absurd hoof (by simp [isOofR])
    | uncaught _ _ => rw [hcase] at hoof; exact absurd hoof (by simp [isOofR])
    | unsupported _ _ => rw [hcase] at hoof; exact absurd hoof (by simp [isOofR])
    | stuck _ _ => rw [hcase] at hoof; exact absurd hoof (by simp [isOofR])
  · have hne : isOofR (Interp.run f (deliverA a m₀ [])) = false := by
      cases hb : isOofR (Interp.run f (deliverA a m₀ [])) with
      | false => rfl
      | true => exact absurd hb hoof
    -- the same answer, found with `rest + f` fuel, runs the escape for `f` steps and more
    have hadd := runA_add fuel m a m₀ rest hr f
    have hrun : Interp.run (fuel + f) m = Interp.run (rest + f) (deliverA a m₀ []) := by
      rw [run_eq_out_nil (fuel + f) m, hadd]; rfl
    have hstable : Interp.run (rest + f) (deliverA a m₀ []) =
        Interp.run f (deliverA a m₀ []) := by
      rw [Nat.add_comm rest f]; exact run_le_eq rest f _ hne
    have := h (fuel + f)
    rw [hrun, hstable] at this
    exact this

/-- A value in flight at an empty continuation is one step from `.done`: the shape every
loop exit and every `break` lands on. -/
theorem safeA_value_nil (m : Machine) (v : Value) :
    SafeA { m with ctl := .value v, kont := [] } := by
  intro f
  match f with
  | 0 => simp [Interp.run, Semantics.typeStuck]
  | f + 1 => simp [Interp.run, Interp.stepFn, Interp.applyKont, Semantics.typeStuck]

#print axioms safe_pushK
#print axioms safe_pushK_le
#print axioms delivers_safeA

end Ratchet.Denote
