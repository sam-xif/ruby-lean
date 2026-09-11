import Denote.Rules.Vasgn

/-!
# `Denote/Rules/VasgnStuck.lean` — the second axis, one rung

**Diagnosis of why this axis exists at all**: `../../../docs/semantics/answer-typed-judgments.md`
(§2.1–§2.2 cite this file).

> **Re-proved 2026-09-11 through the answer type** — `Denote/Rules/VasgnAnswer.lean`, same
> `Prop`, with a cost table comparing the two. `stuckFreeRun_pushK_le` below (86 lines, this
> axis only) is subsumed by `run_pushK` (`Denote/Sem/Answer.lean`, 62 lines, **both** axes),
> and `JumpStuckFree` is deleted rather than shrunk. This file still builds and still holds
> the measurement the change was priced from.

**The experiment.** `Denote/Sem/State.lean` states `StuckFree` and says "nothing in the
ladder uses it yet"; `Denote/Adequacy.lean` states `StuckFreeTarget` and records that it is
**not implied by** `AdequacyTarget`, because `SemJudge` quantifies only over runs that
produced a value. The open question that leaves is *how much a stuck-freedom rung actually
costs*, and the cheapest way to answer it is to prove one. `Judge.vasgn` is the right one:
it is the first compound rung on the value axis (`Denote/Rules/Vasgn.lean`, clink 54), so
its two axes can be compared directly.

## What the experiment found

**1. The obligation does not mention the typing premises.** `Judge.vasgn` carries three
(`capStale`, `capStaleCtx`, `isAliasTy`) and the value-axis proof spends all three. The
stuck-freedom obligation spends **none** of them, and does not even need `StateOk` — writing
a local cannot get stuck whatever the types say. That is the two-axes claim made concrete:
the premises that make `vasgn` *type*-sound are invisible here, and the fact that makes it
*stuck*-free is invisible there.

**2. It needed a new decomposition, and only one.** `run_split` splits a run under an
appended continuation **at the value it delivers** — so it says nothing when the run does
not deliver one, which is every case this axis is about. `stuckFreeRun_pushK` below is its
counterpart: the same induction, concluding over all five `RunResult` arms instead of one.
The `.uncaught` case is where the two differ most, and it is easy for a reason worth
recording: `frameR K (.uncaught exc m) = .uncaught exc m` passes the exception through
**with its machine unchanged**, so the outer run's verdict is literally the inner run's.

**3. The `kont` gap is real but local.** `StuckFree` is stated at `evalFrom`, which sets
`kont := []`, while the sub-run of the right-hand side happens under `[.asgnK .lvar x]`.
That mismatch is exactly what `stuckFreeRun_pushK` bridges, and bridging it needs one side
condition per continuation (`JumpStuckFree`, the `JumpOpaque` of this axis) — for `asgnK`,
four lines, because `unwind`'s default arm pops the frame and hands the jump straight back
to the machine the premise is about.

So: no `KontOk` was required *for this rung*. The honest reading is that `vasgn` pushes a
continuation it immediately consumes, so the invariant never has to describe a machine that
some *other* rule is responsible for. A rule whose sub-run can reach a state typed by a
different rule (a send's argument list, a `seq` tail) is where a continuation typing becomes
unavoidable, and this rung does not settle that.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The side condition — `JumpOpaque`'s counterpart on this axis

`run_split` needs `JumpOpaque K` ("`K` cannot turn an escaping jump into a returned value").
The stuck-freedom decomposition needs the corresponding fact about *this* axis: `K` cannot
turn an escaping jump into a **type-stuck** outcome that the jump did not already have. -/

/-- Delivering a jump to `K` reaches no type-stuck outcome that the same jump at the empty
continuation did not already reach. Like `JumpOpaque`, it holds by computation for every
continuation a `Judge` rule pushes, because those are literals. -/
def JumpStuckFree (K : List Kont) : Prop :=
  ∀ (m : Machine) (j : Jump), m.ctl = .jump j → m.kont = [] →
    (∀ n, Semantics.typeStuck (Interp.run n m) = false) →
    ∀ fuel, Semantics.typeStuck (Interp.run fuel (pushK K m)) = false

/-- `[.asgnK kind x]` is jump-stuck-free: `unwind`'s default arm pops the frame and passes
the jump through, which lands back on the very machine the hypothesis is about. One step,
and then the hypothesis. -/
theorem jumpStuckFree_asgnK (kind : RubyCore.VarKind) (x : String) :
    JumpStuckFree [.asgnK kind x] := by
  intro m j hc hk hin fuel
  match fuel with
  | 0 => simp [Interp.run, Semantics.typeStuck]
  | f + 1 =>
    have hpush : pushK [.asgnK kind x] m = { m with ctl := .jump j, kont := [.asgnK kind x] } := by
      simp only [pushK, hk, List.nil_append, ← hc]
    have hs : Interp.stepFn { m with ctl := .jump j, kont := [.asgnK kind x] }
        = .next (Interp.withCtl { m with ctl := .jump j, kont := [] } (.jump j)) := rfl
    have hm : Interp.withCtl { m with ctl := .jump j, kont := [] } (.jump j) = m := by
      simp only [Interp.withCtl, ← hc, ← hk]
    rw [hpush, Interp.run, hs, hm]
    exact hin f

/-! ## The decomposition

`run_split`'s statement is about the one outcome this axis does not care about. This is the
same induction with the conclusion moved to `typeStuck`. -/

/-- **The run-level frame rule, on the stuck-freedom axis.** A run under an appended
continuation `K` is stuck-free when the inner run is stuck-free and every delivery of an
inner value to `K` is stuck-free.

Compare `run_split`: same three hypotheses in spirit (`CatchFree`, a jump side condition,
and an induction on fuel), and the same case analysis on `m.ctl`. What changes is that the
four non-`.value` step outcomes are no longer contradictions — they are the cases that
carry the result, and each is discharged by `frameR` leaving them alone. -/
theorem stuckFreeRun_pushK_le (K : List Kont) (hK : RubyCore.Proof.CatchFree K)
    (hJ : JumpStuckFree K) :
    ∀ (fuel : Nat) (m : Machine),
      (∀ n, Semantics.typeStuck (Interp.run n m) = false) →
      (∀ (k : Nat) (v₀ : Value) (m₀ : Machine), Interp.run (k + 1) m = .value v₀ m₀ →
        ∀ f, f + k ≤ fuel → Semantics.typeStuck (Interp.run f (deliver m₀ v₀ K)) = false) →
      Semantics.typeStuck (Interp.run fuel (pushK K m)) = false := by
  intro fuel
  induction fuel with
  | zero => intro m _ _; simp [Interp.run, Semantics.typeStuck]
  | succ n ih =>
    intro m hin hout
    rw [Interp.run]
    cases hc : m.ctl with
    | eval e =>
      -- `evalExpr` never reads the continuation, so the frame rule needs no side condition
      have hstep : Interp.stepFn (pushK K m) =
          RubyCore.Proof.frameR K (Interp.stepFn m) := by
        simp only [Interp.stepFn, pushK_eq, RubyCore.Proof.pushK_ctl, hc,
          RubyCore.Proof.evalExpr_frame K hK]
      rw [hstep]
      cases hev : Interp.stepFn m with
      | next m₂ =>
        simp only [RubyCore.Proof.frameR]
        refine ih m₂ (fun k => ?_) (fun k v₀ m₀ hval f hle => ?_)
        · have := hin (k + 1); rwa [Interp.run, hev] at this
        · exact hout (k + 1) v₀ m₀ (by rw [Interp.run, hev]; exact hval) f (by omega)
      | done w m₂ =>
        have h1 := (RubyCore.Proof.done_inv m w m₂ hev).1
        rw [hc] at h1
        exact absurd h1 (by simp)
      | uncaught exc m₂ =>
        -- the exception passes through the frame **with its machine**, so the verdict is
        -- the inner run's, and the hypothesis is exactly that
        simp only [RubyCore.Proof.frameR]
        have := hin (n + 1); rwa [Interp.run, hev] at this
      | unsupported r => simp [RubyCore.Proof.frameR, Semantics.typeStuck]
      | stuck msg => simp [RubyCore.Proof.frameR, Semantics.typeStuck]
    | value w =>
      cases hk : m.kont with
      | nil =>
        -- **the pass-through point**: the inner run ends here, and the rest is a delivery
        have hdel : pushK K m = deliver m w K := pushK_eq_deliver K hc hk
        have : Semantics.typeStuck (Interp.run (n + 1) (deliver m w K)) = false :=
          hout 0 w m (by simp only [Interp.run, Interp.stepFn, hc, Interp.applyKont, hk])
            (n + 1) (by omega)
        rw [← Interp.run, hdel]; exact this
      | cons kk rest =>
        have hne : m.kont ≠ [] := by rw [hk]; simp
        have hstep : Interp.stepFn (pushK K m) =
            RubyCore.Proof.frameR K (Interp.stepFn m) := by
          simp only [Interp.stepFn, pushK_eq, RubyCore.Proof.pushK_ctl, hc,
            RubyCore.Proof.applyKont_frame K hK m w hne]
        rw [hstep]
        cases hev : Interp.stepFn m with
        | next m₂ =>
          simp only [RubyCore.Proof.frameR]
          refine ih m₂ (fun k => ?_) (fun k v₀ m₀ hval f hle => ?_)
          · have := hin (k + 1); rwa [Interp.run, hev] at this
          · exact hout (k + 1) v₀ m₀ (by rw [Interp.run, hev]; exact hval) f (by omega)
        | done w₂ m₂ => exact absurd (RubyCore.Proof.done_inv m w₂ m₂ hev).2.1 hne
        | uncaught exc m₂ =>
          simp only [RubyCore.Proof.frameR]
          have := hin (n + 1); rwa [Interp.run, hev] at this
        | unsupported r => simp [RubyCore.Proof.frameR, Semantics.typeStuck]
        | stuck msg => simp [RubyCore.Proof.frameR, Semantics.typeStuck]
    | jump j =>
      cases hk : m.kont with
      | nil =>
        -- the inner run has escaped; the side condition is exactly this case
        rw [← Interp.run]
        exact hJ m j hc hk hin (n + 1)
      | cons kk rest =>
        have hne : m.kont ≠ [] := by rw [hk]; simp
        have hstep : Interp.stepFn (pushK K m) =
            RubyCore.Proof.frameR K (Interp.stepFn m) := by
          simp only [Interp.stepFn, pushK_eq, RubyCore.Proof.pushK_ctl, hc,
            RubyCore.Proof.unwind_frame K hK m j hne]
        rw [hstep]
        cases hev : Interp.stepFn m with
        | next m₂ =>
          simp only [RubyCore.Proof.frameR]
          refine ih m₂ (fun k => ?_) (fun k v₀ m₀ hval f hle => ?_)
          · have := hin (k + 1); rwa [Interp.run, hev] at this
          · exact hout (k + 1) v₀ m₀ (by rw [Interp.run, hev]; exact hval) f (by omega)
        | done w₂ m₂ => exact absurd (RubyCore.Proof.done_inv m w₂ m₂ hev).2.1 hne
        | uncaught exc m₂ =>
          simp only [RubyCore.Proof.frameR]
          have := hin (n + 1); rwa [Interp.run, hev] at this
        | unsupported r => simp [RubyCore.Proof.frameR, Semantics.typeStuck]
        | stuck msg => simp [RubyCore.Proof.frameR, Semantics.typeStuck]

/-- The unbounded form — what a continuation that is *consumed* rather than re-entered
needs, and what `Judge.vasgn` uses. Two lines from the bounded one: drop the fuel bound.

Both are on file because the bound is what a **back edge** needs and nothing else does
(`Denote/Rules/WhileStuck.lean` §Finding 1: a delivery that re-enters the loop cannot be
discharged at arbitrary fuel without circularity). Keeping one lemma with the bound and one
corollary without it means the two callers share an induction. -/
theorem stuckFreeRun_pushK (K : List Kont) (hK : RubyCore.Proof.CatchFree K)
    (hJ : JumpStuckFree K) :
    ∀ (fuel : Nat) (m : Machine),
      (∀ n, Semantics.typeStuck (Interp.run n m) = false) →
      (∀ (v₀ : Value) (m₀ : Machine), (∃ n, Interp.run n m = .value v₀ m₀) →
        ∀ f, Semantics.typeStuck (Interp.run f (deliver m₀ v₀ K)) = false) →
      Semantics.typeStuck (Interp.run fuel (pushK K m)) = false := fun fuel m hin hout =>
  stuckFreeRun_pushK_le K hK hJ fuel m hin
    (fun k v₀ m₀ hval f _ => hout v₀ m₀ ⟨k + 1, hval⟩ f)

/-! ## The delivery, for `asgnK`

Two steps and no hypotheses: pop the frame and write the local, then deliver to the empty
continuation, which is `.done`. Nothing on that path dispatches, so nothing on it can stick
— which is the whole reason this rung is cheap. -/

theorem deliver_asgnK_stuckFree (m₀ : Machine) (v₀ : Value) (x : String) :
    ∀ f, Semantics.typeStuck (Interp.run f (deliver m₀ v₀ [.asgnK .lvar x])) = false := by
  intro f
  match f with
  | 0 => simp [Interp.run, Semantics.typeStuck]
  | 1 => simp [Interp.run, stepFn_asgnK m₀ x v₀, Semantics.typeStuck]
  | f + 2 =>
    -- `run_succ` rather than `Interp.run`: the second unfolding leaves a matcher standing,
    -- which `rw` cannot see through (the rule `Denote/Sem/notes.md` records twice over).
    simp only [run_succ, stepFn_asgnK m₀ x v₀, stepFn_value_nil]
    simp [Semantics.typeStuck]

/-! ## The obligation, and the rung

Stated in the ladder's shape — one per `Judge` rule, hypotheses mirroring the rule's
premises — so that a second ladder, if it is ever built, has this as its first rung. -/

/-- `StuckFree`, quantified over the machines a context describes: the second axis's
counterpart to `SemJudge`'s `∀ m, StateOk κ Γ I m → …`. -/
def StuckFreeAt (κ : Ctx) (Γ : Env) (I : Ty) (e : Ratchet.Expr) : Prop :=
  ∀ m : Machine, StateOk κ Γ I m → StuckFree m e

/-- The stuck-freedom obligation for `Judge.vasgn`.

**Note what is not here.** `Obl.Judge.vasgn` takes `τ`, `Γ'`, `I'` and the three side
conditions; this takes none of them. An assignment's stuck-freedom is its right-hand side's,
and no typing premise bears on it. -/
def OblStuck.Judge.vasgn : Prop :=
  ∀ (κ : Ctx) (Γ : Env) (I : Ty) (x : String) (e : Ratchet.Expr),
    StuckFreeAt κ Γ I e → StuckFreeAt κ Γ I (.vasgn .lvar x e)

theorem SemStuck.Judge.vasgn : OblStuck.Judge.vasgn := by
  intro κ Γ I x e hprem m hm fuel
  match fuel with
  | 0 => simp [evalFrom, Interp.run, Semantics.typeStuck]
  | f + 1 =>
    -- Step 1: peel the push, leaving a run of `e` under `[.asgnK .lvar x]`.
    rw [Interp.run, stepFn_vasgn_push]
    -- The decomposition, with the premise on one side and the two-step write on the other.
    exact stuckFreeRun_pushK [.asgnK .lvar x] (catchFree_asgnK x)
      (jumpStuckFree_asgnK .lvar x) f (evalFrom m e)
      (hprem m hm)
      (fun v₀ m₀ _ f' => deliver_asgnK_stuckFree m₀ v₀ x f')

/-! ## Non-vacuity, and the shape of a second rung

An obligation whose hypothesis nothing satisfies is worth nothing — the risk
`Denote/Sanity.lean` exists to answer on the other axis. So: a leaf rung, and the two
composed. -/

/-- **The leaf shape.** An expression whose evaluation is one step to a value at the empty
continuation is stuck-free, whatever the machine. `evals_pure`'s hypothesis, reused
verbatim — which is the first sign the two axes can share a vocabulary even where they
cannot share a theorem. -/
theorem stuckFree_pure {m m₁ : Machine} {e : Ratchet.Expr} {w : Value}
    (hstep : Interp.stepFn (evalFrom m e) = .next (reCtl m₁ (.value w) [])) :
    StuckFree m e := by
  intro fuel
  match fuel with
  | 0 => simp [Interp.run, Semantics.typeStuck]
  | 1 => simp [run_succ, hstep, run_zero, Semantics.typeStuck]
  | f + 2 =>
    simp only [run_succ, hstep, stepFn_value_nil]
    simp [Semantics.typeStuck]

/-- `Judge.intLit` on this axis — the whole rung, since a literal cannot stick. -/
theorem SemStuck.Judge.intLit (κ : Ctx) (Γ : Env) (I : Ty) (n : Int) :
    StuckFreeAt κ Γ I (.int n) :=
  fun m _ => stuckFree_pure (m₁ := m) (w := .int n) rfl

/-- The two composed: `x = 1` reaches no type-stuck outcome, from any conformant machine.
Nothing in the hypothesis is discharged by assumption — this is the obligation applied. -/
example (κ : Ctx) (Γ : Env) (I : Ty) (x : String) (n : Int) :
    StuckFreeAt κ Γ I (.vasgn .lvar x (.int n)) :=
  SemStuck.Judge.vasgn κ Γ I x (.int n) (SemStuck.Judge.intLit κ Γ I n)

#print axioms SemStuck.Judge.vasgn
#print axioms SemStuck.Judge.intLit
#print axioms stuckFreeRun_pushK
#print axioms stuckFreeRun_pushK_le

end Ratchet.Denote
