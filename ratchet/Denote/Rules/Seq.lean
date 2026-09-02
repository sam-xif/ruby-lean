import Denote.Rules.Core
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Seq.lean` — the one-statement sequence

`JudgeSeq.last` is the base case of the statement-sequence family, and it is the one member of
that family that is *not* behind `Denote/Sem/notes.md`'s fifth stall point (the continuation
frame). The reason is a fact about `evalExpr`:

```
| .seq es => match es with
  | [e] => .next (withCtl m (.eval e))        -- no continuation pushed
  | e :: rest => .next (withKont m (.eval e) (.seqK rest))
```

A **singleton** sequence pushes nothing. So a run of `.seq [e]` from `m` with an empty
continuation *is* the run of `e` from `m` with an empty continuation, one step later — which is
exactly what `Evals` quantifies over, and no decomposition lemma is needed. `JudgeSeq.cons`,
whose first statement runs under `.seqK rest`, is the case that is still blocked.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **A singleton sequence evaluates its statement, in the same continuation.** One step of
`stepFn` separates the two machines, and `Evals`'s fuel is existential, so the step is free. -/
theorem evals_seq_one {m : Machine} {e : Ratchet.Expr} {v : Value} {m' : Machine}
    (h : Evals m (.seq [e]) v m') : Evals m e v m' := by
  obtain ⟨fuel, hrun⟩ := h
  have hstep : Interp.stepFn (evalFrom m (.seq [e])) = .next (evalFrom m e) := rfl
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | fuel + 1 =>
    rw [run_succ, hstep] at hrun
    exact ⟨fuel, hrun⟩

/-- `SemJudgeSeq` at a singleton is `SemJudge` at the statement, and the step above is the
whole of the difference. -/
theorem Sem.JudgeSeq.last : Obl.JudgeSeq.last := by
  intro κ Γ Γ' I I' e τ hj
  -- the singleton's plainness is the statement's own premise
  refine ⟨fun e' he' => by rcases List.mem_singleton.mp he' with rfl; exact hj.1, ?_⟩
  intro m hm v m' h
  exact hj.2 m hm v m' (evals_seq_one h)

#print axioms Sem.JudgeSeq.last

end Ratchet.Denote
