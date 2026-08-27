/-
  RubyCore.HJudge.Walk — the machine walk, term-level.

  **Ported from `mdd/sorbet-lean/SorbetLean/Walk.lean`** (spike S2).

  The replay engine's core move: `wp_walk_step` is a META-implication between
  entailments, so a replay proof is a chain of `refine wp_walk_step (hf := by
  rfl) ?_` — the successor machine `m'` is COMPUTED by `rfl`-unification
  (whnf of `stepFn` on the loaded configuration; the boot heap is
  kernel-reducible by design). No IPM text appears in replay proofs at all:
  the walk stops by itself where reduction sticks (a branch on a symbolic
  value — exactly where a certificate narrowing step, i.e. a `cases`, enters)
  or where the run terminates (close with `wp_walk_val`/`wp_walk_exc`).

  This is the golean `go_walk` idea collapsed to its degenerate deterministic
  form: one law, matched by unification instead of a DiscrTree, because our
  step is a function.
-/
import RubyCore.HJudge.Rules

set_option autoImplicit false

namespace RubyCore.HJudge

open RubyCore
open Iris Iris.ProgramLogic Iris.BI

variable {GF : BundledGFunctors} [RubyGS GF]
variable {s : Stuckness} {E : CoPset}

/-- One walk step: a `stepFn` equation plus the continuation's entailment
    yields the current entailment. -/
theorem wp_walk_step {c : MCfg} {h : Heap} {m' : Machine}
    {Φ : ROutcome → IProp GF}
    (hf : Interp.stepFn (c.load h) = .next m')
    (Hcont : stateIs (GF := GF) m'.heap ⊢
      WP (RExpr.running m'.cfg) @ s ; E {{ Φ }}) :
    stateIs (GF := GF) h ⊢ WP (RExpr.running c) @ s ; E {{ Φ }} := by
  refine Entails.trans ?_ (wp_step_next hf)
  iintro Hst
  isplitl [Hst]
  · inext
    iexact Hst
  · inext
    iintro Hst'
    iapply Hcont
    iexact Hst'

/-- Terminal walk step, value outcome, pure postcondition. -/
theorem wp_walk_val {c : MCfg} {h : Heap} {v : Value} {m' : Machine}
    {φ : ROutcome → Prop}
    (hf : Interp.stepFn (c.load h) = .done v m')
    (hφ : φ (.val v m'.heap)) :
    stateIs (GF := GF) h ⊢
      WP (RExpr.running c) @ s ; E {{ o, iprop(⌜φ o⌝) }} := by
  refine Entails.trans ?_ (wp_step_val hf)
  iintro Hst
  iframe Hst
  iintro Hst'
  ipureintro
  exact hφ

/-- Terminal walk step, uncaught-exception outcome, pure postcondition. -/
theorem wp_walk_exc {c : MCfg} {h : Heap} {e : Value} {m' : Machine}
    {φ : ROutcome → Prop}
    (hf : Interp.stepFn (c.load h) = .uncaught e m')
    (hφ : φ (.exc e m'.heap)) :
    stateIs (GF := GF) h ⊢
      WP (RExpr.running c) @ s ; E {{ o, iprop(⌜φ o⌝) }} := by
  refine Entails.trans ?_ (wp_step_exc hf)
  iintro Hst
  iframe Hst
  iintro Hst'
  ipureintro
  exact hφ

/-- THE WALK LEMMA, metavariable-free (the shape the tactic drives): the
    continuation obligation is phrased as a `match` on `stepFn`'s result, so
    a single `apply` + one `simp only [rb_eval]` per step advances the
    machine — simp normalizes the scrutinee and iota-reduces the match in
    one pass, and the successor arrives already normalized (no snowballing
    partial-whnf terms). `.unsupported`/`.stuck` demand `False`: the walk
    refuses to cross the fragment boundary, loudly. -/
theorem wp_walk_all {c : MCfg} {h : Heap} {φ : ROutcome → Prop}
    (H : match Interp.stepFn (c.load h) with
      | .next m' =>
          stateIs (GF := GF) m'.heap ⊢
            WP (RExpr.running m'.cfg) @ s ; E {{ o, iprop(⌜φ o⌝) }}
      | .done v m' => φ (.val v m'.heap)
      | .uncaught e m' => φ (.exc e m'.heap)
      | .unsupported _ => False
      | .stuck _ => False) :
    stateIs (GF := GF) h ⊢
      WP (RExpr.running c) @ s ; E {{ o, iprop(⌜φ o⌝) }} := by
  cases hstep : Interp.stepFn (c.load h) <;> rw [hstep] at H
  case next m' => exact wp_walk_step hstep H
  case done v m' => exact wp_walk_val hstep H
  case uncaught e m' => exact wp_walk_exc hstep H
  case unsupported r => exact absurd H (by intro h; exact h)
  case stuck msg => exact absurd H (by intro h; exact h)

/-- One machine step: apply the walk lemma, then materialize the scrutinee
    (cheap `simp only`; guard/heap residue is left to defeq). Fails cleanly at
    a dispatch (whnf-opaque `invoke`) — `rb_dispatch` crosses those — and at a
    terminal, where the goal is the pure `φ` fact by defeq. -/
macro "rb_step" : tactic =>
  `(tactic|
    (apply wp_walk_all
     try (conv in Interp.stepFn _ => simp only [rb_eval])))

/-- Cross one dispatch: `invoke` is opaque to whnf (WF recursion), so unfold
    it by its equation, then its `where`-bound dispatcher; everything else
    reduces by defeq. (T5's `dispatch_progress` recipe, walk-shaped.) -/
macro "rb_dispatch" : tactic =>
  `(tactic|
    (rw [Interp.invoke.eq_def]
     simp only [Interp.invoke.invokeDispatch]))

/-- The full walk: steps and dispatches until a terminal or a genuinely
    symbolic branch. CAUTION: on arguments whose comparisons cannot reduce
    (an abstract `Int` rather than a constructor form) this can churn — split
    on constructor forms FIRST (the certificate's narrowing step). -/
macro "rb_walk" : tactic =>
  `(tactic| repeat (first | rb_step | rb_dispatch))

end RubyCore.HJudge
