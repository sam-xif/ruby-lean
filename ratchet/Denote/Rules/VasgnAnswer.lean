import Denote.Sem.SafeKont
import Denote.Rules.VasgnStuck

/-!
# `Denote/Rules/VasgnAnswer.lean` — `Judge.vasgn`'s stuck-freedom rung, re-proved through the
answer type

The control experiment. `Denote/Rules/VasgnStuck.lean` proves exactly this theorem the
projection way; this file proves it again from `Denote/Sem/SafeKont.lean`, so the two costs
can be read side by side rather than argued about.

| component | projection (`VasgnStuck.lean`) | answer (`Answer.lean` + this) |
|---|---|---|
| the decomposition | `stuckFreeRun_pushK_le`, 92 lines, **stuck axis only** | `run_pushK`, 70 lines, **both axes** |
| the jump side condition | `JumpStuckFree` + `jumpStuckFree_asgnK`, 22 lines | the `esc` clause below, **4 lines** |
| the value delivery | `deliver_asgnK_stuckFree`, 12 lines | unchanged, reused |
| the rung | 16 lines | 12 lines |

The interesting row is the second. `jumpStuckFree_asgnK` and the `esc` clause below prove the
*same computation* — `unwind`'s default arm pops the frame and hands the jump back — but the
side-condition version has to quantify over every machine whose own run happens to be
stuck-free, because there is nothing else for it to say. The clause version receives the
escape together with the fact that it came from a stuck-free sub-run, which is all the
computation ever needed. The difference is worth nothing here and is the whole difference at
a loop (`WhileAnswer.lean`).
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **The `esc` clause for `asgnK`.** `unwind`'s default arm pops the frame and passes the
jump through, landing on `deliverA (.esc j) m₀ []` — the very machine the hypothesis is
about. One step. -/
theorem safeKont_asgnK_esc (m₀ : Machine) (j : Jump) (x : String)
    (h : SafeA (deliverA (.esc j) m₀ [])) :
    ∀ f, Semantics.typeStuck (Interp.run f (deliverA (.esc j) m₀ [.asgnK .lvar x])) = false := by
  intro f
  match f with
  | 0 => simp [run_zero, Semantics.typeStuck]
  | f + 1 => rw [run_succ]; exact h f

/-- `Judge.vasgn` on the stuck-freedom axis, through `safe_pushK`. Same statement as
`SemStuck.Judge.vasgn`; the `val` and `esc` arms are the two clauses, side by side. -/
theorem SemStuckA.Judge.vasgn : OblStuck.Judge.vasgn := by
  intro κ Γ I x e hprem m hm fuel
  match fuel with
  | 0 => simp [evalFrom, run_zero, Semantics.typeStuck]
  | f + 1 =>
    rw [run_succ, stepFn_vasgn_push]
    refine safe_pushK (Q := fun r => Semantics.typeStuck r = false) (catchFree_asgnK x)
      haltBlind_stuck oof_stuck (hprem m hm) (delivers_safeA (hprem m hm)) ?_ f
    intro a m₀ hsafe f'
    cases a with
    | val v => exact deliver_asgnK_stuckFree m₀ v x f'
    | esc j => exact safeKont_asgnK_esc m₀ j x hsafe f'

/-- The two rungs agree: this is the same `Prop`, so the ladder cannot tell them apart. -/
example : OblStuck.Judge.vasgn := SemStuckA.Judge.vasgn
example : OblStuck.Judge.vasgn := SemStuck.Judge.vasgn

#print axioms SemStuckA.Judge.vasgn

end Ratchet.Denote
