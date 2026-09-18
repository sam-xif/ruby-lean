import Denote.Sem.Core.Decompose

/-!
# `Denote/Sem/Core/Answer.lean` — the answer type, and the one equation that replaces the ladder's
two decompositions

**Design**: `../../AGENTS.md` §The answer-typed design §6. This file is that
proposal's first half, built: `Answer`, the answer-producing run `runA`, and the master
equation `run_pushK`.

## The diagnosis, in one line

`Interp.run` answers five ways and every decomposition in this package reads **one** of them.
`run_split` (`Denote/Sem/Core/Decompose.lean`) splits a run at the `.value` it delivers and needs
`JumpOpaque K` to rule the other four out; `stuckFreeRun_pushK_le`
(`Denote/Rules/VasgnStuck.lean`) is the same 92-line induction with the conclusion moved to
`typeStuck` and needs `JumpStuckFree K`, which is **false** at a loop continuation
(`Denote/Rules/WhileStuck2.lean`). Two inductions, two side conditions, one of them
unsatisfiable.

## The fix

Split the run at the state where it hands control back, whatever it is handing back. That
state is characterised by `answerPoint`: an empty continuation with either a value or a jump
in flight. The two are the arms of `Answer`, and `runA` is `Interp.run` stopped there instead
of run through it.

Then the decomposition is not a lemma with hypotheses, it is an **equation**:

    Interp.run fuel (pushK K m) = (runA fuel m).out K          -- `run_pushK`, `CatchFree K`

`CatchFree` survives — it is a fact about `stepFn` (a `throw` reads the whole continuation),
not about the projection, and §7 of the design note says so. Everything else goes: no
`JumpOpaque`, no `JumpStuckFree`, no per-axis induction. A rung picks its property `Q`,
case-splits the three arms of `ARes`, and the arm it used to have to *exclude* is now the arm
it *discharges*.

## Why `Halt` carries the machine

`Interp.run`'s `.unsupported`/`.stuck` arms report the machine **before** the step, so under
`pushK K` they report a machine with `K` on it — the results differ in a field nothing reads,
and an equation has to say so rather than hand-wave it. `Halt.out` is that bookkeeping, and
it is the reason `run_pushK` is an equality rather than a five-way implication.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The answer type -/

/-- **What a sub-computation hands back.** Ueno et al.'s packed value, CakeML's
`Rval | Rerr`, and `Interp.run`'s own five-way split, restricted to the two outcomes that are
*handed to a continuation*: a returned value, or a jump in flight.

The `gate` arm the design note floated (§6, §8's second open question) is **not** here, and
that is a finding rather than an omission: `.unsupported` is not delivered to anything — it
aborts the run — so it belongs with `.stuck` in `Halt`, not in `Answer`. Answers are what a
continuation *consumes*; halts are what ends the program regardless of what is below. -/
inductive Answer where
  | val (v : Value)
  | esc (j : Jump)
deriving Inhabited

/-- The control word an answer is in flight as. -/
def Answer.ctl : Answer → Ctl
  | .val v => .value v
  | .esc j => .jump j

/-- **The answer point**: an empty continuation with something in flight. These are exactly
the two states `RubyCore.Proof.stepFn_frame`'s side condition excludes — i.e. exactly the
states at which appending a continuation changes what happens next — which is why they are
the right place to cut. -/
def answerPoint (m : Machine) : Option Answer :=
  match m.kont with
  | [] =>
    match m.ctl with
    | .value v => some (.val v)
    | .jump j => some (.esc j)
    | .eval _ => none
  | _ :: _ => none

/-- Handing answer `a` to continuation `K` from machine `m`. Generalises
`Denote/Sem/Core/Decompose.lean`'s `deliver`, which is the `val` arm. -/
def deliverA (a : Answer) (m : Machine) (K : List Kont) : Machine :=
  { m with ctl := a.ctl, kont := K }

theorem deliverA_val (m : Machine) (v : Value) (K : List Kont) :
    deliverA (.val v) m K = deliver m v K := rfl

/-- An outcome that is **not** handed to anything: the run is over whatever is below it.
`.unsupported` and `.stuck` carry the pre-step machine, which is why the continuation has to
be re-applied when the halt is reported from inside a `pushK`. -/
inductive Halt where
  | uncaught (exc : Value) (m : Machine)
  | unsupported (reason : String) (m : Machine)
  | stuck (msg : String) (m : Machine)

/-- The result of running to the next answer. -/
inductive ARes where
  | ans (a : Answer) (m : Machine) (rest : Nat)
  | halt (h : Halt)
  | oof (m : Machine)

/-- **`Interp.run`, stopped at the answer point.** Identical to `Interp.run` except that it
does not step *through* an empty-continuation value or jump — it reports it, with the fuel
that was left. -/
def runA (fuel : Nat) (m : Machine) : ARes :=
  match answerPoint m with
  | some a => .ans a m fuel
  | none =>
    match fuel with
    | 0 => .oof m
    | f + 1 =>
      match Interp.stepFn m with
      | .next m' => runA f m'
      -- unreachable: `done_inv` puts `.done` at an answer point, and this branch is not one
      | .done v m' => .ans (.val v) m' f
      | .uncaught exc m' => .halt (.uncaught exc m')
      | .unsupported r => .halt (.unsupported r m)
      | .stuck msg => .halt (.stuck msg m)

/-- What a halt looks like from outside a `pushK K`. -/
def Halt.out (K : List Kont) : Halt → Interp.RunResult
  | .uncaught exc m => .uncaught exc m
  | .unsupported r m => .unsupported r (pushK K m)
  | .stuck msg m => .stuck msg (pushK K m)

/-- **The reassembly.** Given what the inner computation did, what the run under `K` is. -/
def ARes.out (K : List Kont) : ARes → Interp.RunResult
  | .ans a m rest => Interp.run rest (deliverA a m K)
  | .halt h => h.out K
  | .oof m => .outOfFuel (pushK K m)

/-! ## Unfolding lemmas -/

theorem runA_ans {m : Machine} {a : Answer} (h : answerPoint m = some a) (fuel : Nat) :
    runA fuel m = .ans a m fuel := by
  rw [runA.eq_def, h]

theorem runA_zero {m : Machine} (h : answerPoint m = none) : runA 0 m = .oof m := by
  rw [runA.eq_def, h]

theorem runA_succ {m : Machine} (h : answerPoint m = none) (f : Nat) :
    runA (f + 1) m =
      (match Interp.stepFn m with
       | .next m' => runA f m'
       | .done v m' => .ans (.val v) m' f
       | .uncaught exc m' => .halt (.uncaught exc m')
       | .unsupported r => .halt (.unsupported r m)
       | .stuck msg => .halt (.stuck msg m)) := by
  rw [runA, h]

/-- The side condition `RubyCore.Proof.stepFn_frame` wants **is** "not an answer point". That
coincidence is the whole reason the cut is at the right place, and it is a two-line proof. -/
theorem hside_of_none {m : Machine} (h : answerPoint m = none) :
    m.kont ≠ [] ∨ ∃ e, m.ctl = .eval e := by
  cases hk : m.kont with
  | cons k rest => exact Or.inl (by simp)
  | nil =>
    cases hc : m.ctl with
    | eval e => exact Or.inr ⟨e, rfl⟩
    | value v => rw [answerPoint, hk] at h; simp only at h; rw [hc] at h; simp at h
    | jump j => rw [answerPoint, hk] at h; simp only at h; rw [hc] at h; simp at h

/-- `stepFn`'s frame rule in `frameR` form — the shape `Denote/Sem/Core/Decompose.lean` re-derived
in each of its six branches. -/
theorem stepFn_frameR (K : List Kont) (hK : RubyCore.Proof.CatchFree K) (m : Machine)
    (hside : m.kont ≠ [] ∨ ∃ e, m.ctl = .eval e) :
    Interp.stepFn (pushK K m) = RubyCore.Proof.frameR K (Interp.stepFn m) := by
  cases hc : m.ctl with
  | eval e =>
    simp only [Interp.stepFn, pushK_eq, RubyCore.Proof.pushK_ctl, hc,
      RubyCore.Proof.evalExpr_frame K hK]
  | value v =>
    have hne : m.kont ≠ [] := by
      rcases hside with h | ⟨e, he⟩
      · exact h
      · rw [hc] at he; exact absurd he (by simp)
    simp only [Interp.stepFn, pushK_eq, RubyCore.Proof.pushK_ctl, hc,
      RubyCore.Proof.applyKont_frame K hK m v hne]
  | jump j =>
    have hne : m.kont ≠ [] := by
      rcases hside with h | ⟨e, he⟩
      · exact h
      · rw [hc] at he; exact absurd he (by simp)
    simp only [Interp.stepFn, pushK_eq, RubyCore.Proof.pushK_ctl, hc,
      RubyCore.Proof.unwind_frame K hK m j hne]

/-! ## The master equation -/

/-- **The decomposition, total.** One equation, one hypothesis, five outcomes accounted for.

Compare what it replaces. `run_split` is this restricted to the `.value` arm, with
`JumpOpaque K` supplied to kill the `esc` answer and the four abnormal outcomes silently
dropped; `stuckFreeRun_pushK_le` is this restricted to `typeStuck`, with `JumpStuckFree K`
supplied for the same purpose and a fuel-bound bolted on because a back edge needs one. Here
the `esc` answer is returned rather than excluded, the fuel left over is returned rather than
bounded, and nothing is dropped — so both of those lemmas are corollaries and both side
conditions are gone. -/
theorem run_pushK (K : List Kont) (hK : RubyCore.Proof.CatchFree K) :
    ∀ (fuel : Nat) (m : Machine), Interp.run fuel (pushK K m) = (runA fuel m).out K := by
  intro fuel
  induction fuel with
  | zero =>
    intro m
    cases hap : answerPoint m with
    | some a =>
      rw [runA_ans hap]
      simp only [ARes.out]
      -- `pushK K m` *is* the delivery state: that is what an answer point is
      have : pushK K m = deliverA a m K := by
        cases hk : m.kont with
        | cons k r => rw [answerPoint, hk] at hap; simp at hap
        | nil =>
          cases hc : m.ctl with
          | eval e => rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap; simp at hap
          | value v =>
            rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap
            simp only [Option.some.injEq] at hap
            subst hap
            simp only [pushK, deliverA, Answer.ctl, hk, List.nil_append, ← hc]
          | jump j =>
            rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap
            simp only [Option.some.injEq] at hap
            subst hap
            simp only [pushK, deliverA, Answer.ctl, hk, List.nil_append, ← hc]
      rw [this]
    | none => rw [runA_zero hap]; rfl
  | succ n ih =>
    intro m
    cases hap : answerPoint m with
    | some a =>
      rw [runA_ans hap]
      simp only [ARes.out]
      have : pushK K m = deliverA a m K := by
        cases hk : m.kont with
        | cons k r => rw [answerPoint, hk] at hap; simp at hap
        | nil =>
          cases hc : m.ctl with
          | eval e => rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap; simp at hap
          | value v =>
            rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap
            simp only [Option.some.injEq] at hap
            subst hap
            simp only [pushK, deliverA, Answer.ctl, hk, List.nil_append, ← hc]
          | jump j =>
            rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap
            simp only [Option.some.injEq] at hap
            subst hap
            simp only [pushK, deliverA, Answer.ctl, hk, List.nil_append, ← hc]
      rw [this]
    | none =>
      rw [runA_succ hap, Interp.run, stepFn_frameR K hK m (hside_of_none hap)]
      cases hev : Interp.stepFn m with
      | next m₂ => simp only [RubyCore.Proof.frameR]; exact ih m₂
      | done v m₂ =>
        -- `.done` only happens at an answer point, and this branch is not one
        exfalso
        obtain ⟨hc, hk, -⟩ := RubyCore.Proof.done_inv m v m₂ hev
        rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap; simp at hap
      | uncaught exc m₂ => simp only [RubyCore.Proof.frameR]; rfl
      | unsupported r => simp only [RubyCore.Proof.frameR]; rfl
      | stuck msg => simp only [RubyCore.Proof.frameR]; rfl

/-! ## The answer-level master equation

`run_pushK` relates `Interp.run` under a pushed continuation to the inner `runA`. The
*answer-typed* obligations (`Denote/Judgment/JudgeA.lean`) are stated over `runA` on both sides,
so they need the same equation at the `runA` level — which is this, and it is `run_pushK`'s
proof with `Interp.run` replaced by `runA` and `ARes.out` by `resOutA`.

One lemma gates four rules: `vasgn`, `seq`, `prim` and `if'` all evaluate a sub-expression
under a frame they just pushed, and the premise they hold is about that sub-expression at an
**empty** continuation (`evalFrom` empties it). -/

/-- A halt, seen from outside a pushed continuation. `.uncaught` reports the machine *after*
`unwind` has emptied the stack, so the continuation is already gone from it; the other two
report the pre-step machine, which under `pushK` is the pushed one. Mirrors `Halt.out`. -/
def Halt.underK (K : List Kont) : Halt → Halt
  | .uncaught exc m => .uncaught exc m
  | .unsupported r m => .unsupported r (pushK K m)
  | .stuck msg m => .stuck msg (pushK K m)

/-- What running under a pushed continuation does to an `ARes`. The `ans` arm is the content:
the inner computation reaches an answer, and the outer run continues by delivering that answer
to `K` with the fuel that was left. -/
def resOutA (K : List Kont) : ARes → ARes
  | .ans a m rest => runA rest (deliverA a m K)
  | .halt h => .halt (h.underK K)
  | .oof m => .oof (pushK K m)

/-- Pushing a continuation onto a machine that is **not** at an answer point leaves it not at
one: an answer point has an empty continuation, and `pushK` only ever appends. -/
theorem answerPoint_pushK_none {m : Machine} (K : List Kont) (h : answerPoint m = none) :
    answerPoint (pushK K m) = none := by
  cases hk : m.kont with
  | cons k r => simp [answerPoint, pushK, hk]
  | nil =>
    cases hc : m.ctl with
    | eval e => cases K <;> simp [answerPoint, pushK, hk, hc]
    | value v => rw [answerPoint, hk] at h; simp only at h; rw [hc] at h; simp at h
    | jump j => rw [answerPoint, hk] at h; simp only at h; rw [hc] at h; simp at h

/-- At an answer point, pushing the continuation **is** delivering the answer to it. Shared by
`run_pushK` and `runA_pushK`, which each had their own copy of this three-case argument. -/
theorem pushK_eq_deliverA {m : Machine} {a : Answer} (K : List Kont)
    (hap : answerPoint m = some a) : pushK K m = deliverA a m K := by
  cases hk : m.kont with
  | cons k r => rw [answerPoint, hk] at hap; simp at hap
  | nil =>
    cases hc : m.ctl with
    | eval e => rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap; simp at hap
    | value v =>
      rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap
      simp only [Option.some.injEq] at hap
      subst hap
      simp only [pushK, deliverA, Answer.ctl, hk, List.nil_append, ← hc]
    | jump j =>
      rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap
      simp only [Option.some.injEq] at hap
      subst hap
      simp only [pushK, deliverA, Answer.ctl, hk, List.nil_append, ← hc]

/-- **The answer-level master equation.** Same induction as `run_pushK`, same one hypothesis
(`CatchFree K` — a `catchK` intercepts, so the frame rule does not hold through it), same five
outcomes accounted for. -/
theorem runA_pushK (K : List Kont) (hK : RubyCore.Proof.CatchFree K) :
    ∀ (fuel : Nat) (m : Machine), runA fuel (pushK K m) = resOutA K (runA fuel m) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m
    cases hap : answerPoint m with
    | some a =>
      rw [runA_ans hap, pushK_eq_deliverA K hap]
      simp only [resOutA]
    | none =>
      rw [runA_zero hap, runA_zero (answerPoint_pushK_none K hap)]
      simp only [resOutA]
  | succ n ih =>
    intro m
    cases hap : answerPoint m with
    | some a =>
      rw [runA_ans hap, pushK_eq_deliverA K hap]
      simp only [resOutA]
    | none =>
      rw [runA_succ hap, runA_succ (answerPoint_pushK_none K hap),
        stepFn_frameR K hK m (hside_of_none hap)]
      cases hev : Interp.stepFn m with
      | next m₂ => simp only [RubyCore.Proof.frameR]; exact ih m₂
      | done v m₂ =>
        exfalso
        obtain ⟨hc, hk, -⟩ := RubyCore.Proof.done_inv m v m₂ hev
        rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap; simp at hap
      | uncaught exc m₂ => simp only [RubyCore.Proof.frameR, resOutA, Halt.underK]
      | unsupported r => simp only [RubyCore.Proof.frameR, resOutA, Halt.underK]
      | stuck msg => simp only [RubyCore.Proof.frameR, resOutA, Halt.underK]

#print axioms runA_pushK

/-- The equation at the empty continuation: `runA` is `Interp.run` with the answer point
named. This is what lets a premise stated over the *inner* run (`StuckFree`, `Evals`) be
consumed by a rule reasoning about the outer one. -/
theorem run_eq_out_nil (fuel : Nat) (m : Machine) :
    Interp.run fuel m = (runA fuel m).out [] := by
  have h := run_pushK [] (by intro k hk; exact absurd hk (by simp)) fuel m
  simpa [pushK] using h

#print axioms run_pushK

end Ratchet.Denote
