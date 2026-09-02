import Denote.Rules.Core
import Denote.Sem.Decompose

/-!
# `Denote/Rules/Vasgn.lean` — the first compound rung

`Judge.vasgn` is the rule the fifth stall point was measured on (`../Sem/notes.md`), and this
is it discharged. Everything hard is elsewhere: the interpreter's frame rule and the run-level
decomposition are in `../Sem/Decompose.lean` (over `RubyCore/Proof/KontFrame*.lean`), and the
soundness premise the attempt turned up is `found-issues.md` §F5. What is left here is the
shape the ladder has used since the literals — invert the run, use the premise, transport
across the write — with the decomposition standing in for "invert the run".

## The four steps, and where each comes from

```
eval (vasgn lvar x e)   ⟶ withKont: eval e, kont [asgnK lvar x]      -- `stepFn_vasgn_push`
                        ⟶ … the sub-run of `e` …                     -- `run_split`
                        ⟶ deliver v₀ to asgnK: setLocal x v₀         -- `stepFn_asgnK`
                        ⟶ applyKont []: done                         -- `run_two`
```

The middle line is the whole content: the sub-run is a run of `e` under the *empty*
continuation, which is what the premise `SemJudge κ Γ I e τ Γ' I'` is about.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The two ends of the run -/

/-- The first step: assignment pushes `asgnK` and turns to the right-hand side — and the
machine it turns to is exactly `evalFrom m e` under the pushed continuation, which is what
lets `run_split` apply. `rfl`. -/
theorem stepFn_vasgn_push (m : Machine) (x : String) (e : Ratchet.Expr) :
    Interp.stepFn (evalFrom m (.vasgn .lvar x e))
      = .next (pushK [.asgnK .lvar x] (evalFrom m e)) := rfl

/-- **The two-step tail inversion**, `evals_pure`'s argument at an arbitrary starting machine
rather than at `evalFrom m e`: one step to a value under the empty continuation, and a run
that returned returned that. -/
theorem run_two {m₀ m₁ : Machine} {w v : Value} {m' : Machine}
    (hstep : Interp.stepFn m₀ = .next (reCtl m₁ (.value w) []))
    (h : ∃ f, Interp.run f m₀ = .value v m') :
    v = w ∧ m' = reCtl m₁ (.value w) [] := by
  obtain ⟨fuel, hrun⟩ := h
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | 1 => simp only [run_succ, hstep, run_zero] at hrun; exact absurd hrun (by simp)
  | fuel + 2 =>
    simp only [run_succ, hstep, stepFn_value_nil] at hrun
    cases hrun
    exact ⟨rfl, rfl⟩

/-- `[.asgnK .lvar x]` carries no `catch` marker. -/
theorem catchFree_asgnK (x : String) :
    RubyCore.Proof.CatchFree [.asgnK .lvar x] := by
  intro k hk t
  rcases List.mem_singleton.mp hk with rfl
  simp

/-! ## The rung -/

theorem Sem.Judge.vasgn : Obl.Judge.vasgn := by
  intro κ Γ Γ' I I' x e τ hprem hcap hctx halias m hm v m' hev
  obtain ⟨fuel, hrun⟩ := hev
  -- **Step 1**: peel the push, leaving a run of `e` under `[.asgnK .lvar x]`.
  have hpush : ∃ f, Interp.run f (pushK [.asgnK .lvar x] (evalFrom m e)) = .value v m' := by
    match fuel with
    | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
    | f + 1 =>
      refine ⟨f, ?_⟩
      simpa only [run_succ, stepFn_vasgn_push] using hrun
  obtain ⟨f, hf⟩ := hpush
  -- **The decomposition**: the sub-run of `e` returns, and the rest continues from the
  -- state that delivers its value to `asgnK`.
  obtain ⟨n, v₀, m₀, hin, hout⟩ :=
    run_split [.asgnK .lvar x] (catchFree_asgnK x) (jumpOpaque_asgnK .lvar x) f
      (evalFrom m e) v m' hf
  -- **The tail**: two steps — the write, then the end of the run.
  obtain ⟨rfl, rfl⟩ := run_two (stepFn_asgnK m₀ x v₀) hout
  -- **The premise**, at the sub-run.
  obtain ⟨hstack, hden, hSt'⟩ := hprem m hm v₀ m₀ ⟨n, hin⟩
  -- From here it is `vasgnAlias`'s ending: the write, and the two transports over it.
  let M : Machine := reCtl m₀ (.value v₀) []
  have hMok : StateOk κ Γ' I' M := StateOk_reCtl hSt' _ _
  have hdenM : denM τ M v₀ := denM_reCtl.mpr hden
  refine ⟨?_, ?_, ?_⟩
  · show ((M.setLocal x v₀).stack) = m.stack
    rw [setLocal_stack]
    show m₀.stack = m.stack
    exact hstack
  · exact denM_reCtl.mpr (denM_setLocal hdenM hcap hdenM)
  · refine StateOk_reCtl (StateOk_setLocal hMok hdenM hcap hctx ?_ ?_) _ _
    · -- `τ` is not an alias (§F5), so stripping is the identity
      cases τ <;> simp_all [Ratchet.stripAlias, Ratchet.isAliasTy]
    · -- …and for the same reason there is no alias claim to discharge
      intro y σ hy
      rw [hy] at halias
      simp [Ratchet.isAliasTy] at halias

#print axioms Sem.Judge.vasgn

end Ratchet.Denote
