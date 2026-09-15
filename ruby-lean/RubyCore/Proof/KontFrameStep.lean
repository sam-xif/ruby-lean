import RubyCore.Proof.KontFrameKont

/-!
# `RubyCore/Proof/KontFrameStep.lean` — the top of the framing chain

`evalDefined`, `evalExpr`, and `stepFn`. The chain that starts in `Builtins` ends here, and the
statement it ends in is the one the run-level decomposition consumes:

    stepFn m = .next m₂  →  stepFn (pushK K m) = .next (pushK K m₂)

**The hypothesis is the interesting part.** It is not "`m.kont ≠ []`" but "this step is a real
step" — and it is exactly right. The three step results that are *not* `.next` are the ones
that read the empty continuation as "the program is over": `.done` (a value with nothing left
to do), `.uncaught` (a raise with no handler). Under a pushed `K` those become steps into `K`,
which is precisely what a decomposition wants — so it must not be an equation, and the
hypothesis `stepFn m = .next m₂` is what excludes them without naming them.
-/

set_option autoImplicit false
set_option maxRecDepth 400000

namespace RubyCore
namespace Proof

open Builtins
open Interp

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem evalDefined_frame (K : List Kont) (m : Machine) (e : Expr) :
    evalDefined (pushK K m) e = frameR K (evalDefined m e) := by
  rw [evalDefined.eq_def, evalDefined.eq_def]
  frame_simp
  (repeat' first
    | rfl
    | (frame_simp; done)
    | simp only [frameLem]
    | dsimp only
    | (rw [mk_push K]; try rfl)
    | (rw [withCtl_mk K]; try rfl)
    | (rw [withKont_mk K]; try rfl)
    | split)
  frame_close K

/-! ### `evalExpr`

43 arms, and the strategy matters more here than anywhere else in the chain. Running the full
walker on every arm costs **20 minutes and still times out** at 40M heartbeats. What the arms
actually need was measured in `Denote/Sem/notes.md` §The fifth stall point and holds up: every
arm whose body does not *delegate* closes on `frame_simp; rfl`, and the residue is **one goal
per helper function** — thirteen of them, listed below. So the tactic is a stage per named
callee rather than a search: no `split`, no `simp_all`, and it runs in seconds.

`applyKont` and `unwind` are **not** in that list: `evalExpr` never calls either (the two
places their names appear in `Interp.lean` are comments — "the body below is `applyKont`'s
`defsK` arm verbatim"). That is why this lemma needs no side condition at all, and why
`stepFn`'s below needs one only for the `jump` arm. -/

-- the budget is for the **kernel**, not the tactic: the proof term for 43 arms is large, and
-- at 4M the elaborated declaration times out in `whnf` while being checked
set_option maxHeartbeats 40000000 in
theorem evalExpr_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (e : Expr) :
    evalExpr (pushK K m) e = frameR K (evalExpr m e) := by
  rw [evalExpr.eq_def, evalExpr.eq_def]
  cases e
  all_goals (try (frame_simp; try rfl))
  all_goals (try (rw [startArgs_frame K hK]; try rfl))
  all_goals (try (rw [startSuperArgs_frame K hK]; try rfl))
  all_goals (try (rw [startKwargs_frame K hK]; try rfl))
  all_goals (try (rw [finishSend_frame K hK]; try rfl))
  all_goals (try (rw [doSuper_frame K hK]; try rfl))
  all_goals (try (rw [invoke_frame K hK]; try rfl))
  all_goals (try (rw [mk_push K]; try rfl))
  all_goals (try (rw [withCtl_mk K]; try rfl))
  all_goals (try (rw [withKont_mk K]; try rfl))
  all_goals (try (frame_simp; try rfl))
  -- the `alias` arm's two branches (`undefAliasMiss` vs the rename) are an `if` on a
  -- machine-free condition, so one `split` finishes it
  all_goals (try (split <;> (try (rw [withCtl_mk K])) <;> (try (frame_simp; try rfl))))
  all_goals (try (kont_walk K hK))
  all_goals (try (frame_close K))

/-! ### `stepFn`, and the side condition that is really needed

The first statement tried here was that `stepFn m = .next m₂` alone suffices — the idea being
that the step results it excludes are exactly the ones that read an empty continuation as "the
program is over". That is **false**, and `unwind`'s `retJ` arm is the counterexample: a
non-lambda block `return` whose home method has already exited, met at an *empty*
continuation, does not escape — it steps, to
`raiseErr … "unexpected return"`. Under a pushed `K` the same state instead unwinds into `K`.
So the two sides both step, and to different machines.

Hence the side condition `Denote/Sem/notes.md` states for `KontFrame`: the continuation is
non-empty, or the machine is evaluating (where `evalExpr` never reads the continuation at
all). At an empty continuation with a `.value` the hypothesis `= .next m₂` still does the
work by itself — `applyKont []` is `.done` — so only the jump case needs it. -/

theorem stepFn_frame (K : List Kont) (hK : CatchFree K) (m m₂ : Machine)
    (hside : m.kont ≠ [] ∨ ∃ e, m.ctl = .eval e)
    (h : stepFn m = .next m₂) :
    stepFn (pushK K m) = .next (pushK K m₂) := by
  cases hc : m.ctl with
  | eval e =>
    simp only [stepFn, hc, evalExpr_frame K hK] at h ⊢
    rw [h]
    rfl
  | value v =>
    simp only [stepFn, hc] at h ⊢
    -- the continuation cannot be empty here whatever `hside` says: `applyKont` at `[]` is
    -- `.done`, not `.next`
    have hne : m.kont ≠ [] := by
      intro hk
      rw [applyKont.eq_def, hk] at h
      exact absurd h (by simp)
    rw [applyKont_frame K hK m v hne, h]
    rfl
  | jump j =>
    simp only [stepFn, hc] at h ⊢
    have hne : m.kont ≠ [] := by
      rcases hside with hne | ⟨e, he⟩
      · exact hne
      · rw [hc] at he; exact absurd he (by simp)
    rw [unwind_frame K hK m j hne, h]
    rfl

#print axioms evalDefined_frame
#print axioms evalExpr_frame
#print axioms stepFn_frame

end Proof
end RubyCore
