import Denote.Rules.Core
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Asgn.lean` — the rung that assignment's soundness fix was for

`Judge.vasgnAlias` — `__dt_t1 = x`, the desugarer's own temporary bound to a local — is the
first rule on the ladder that **writes** to the machine's frames, and the first whose
soundness had to be *fixed* before it could be discharged: `found-issues.md` §F1, the
`Ty.clos` capture that a reassignment invalidates. It is discharged here, and the proof is
where the fix earns its keep — `capStale`, the function `Judge.vasgn` uses to decide which
bindings to widen, is the *side condition* of `denM_setLocal` (`Denote/Local.lean`). The
checker's guard and the semantic transport are one predicate.

## Why this rule and not `Judge.vasgn`

`vasgn` assigns an arbitrary expression, whose evaluation runs under a **pushed
continuation** (`withKont m (.eval rhs) (.asgnK …)`), and its premise `SemJudge … e …` is
about a run under the *empty* one. Consuming it needs the continuation-decomposition lemma —
`../Sem/notes.md` §The fifth stall point, which is a fact about `RubyCore`'s abstract machine
and gates every compound rung. `vasgnAlias`'s right-hand side is a `.var`, so the whole run is
four concrete `stepFn` steps and no such lemma is needed. Discharging it is therefore the
sharpest available statement of what is and is not blocked: the *rule* is sound and provably
so; the *general* assignment rule waits on a machine lemma, not on assignment.

## The four steps

```
eval (vasgn lvar t (var lvar x))   ⟶ withKont: eval (var lvar x), kont [asgnK lvar t]
                                   ⟶ value (m.getLocal x),        kont [asgnK lvar t]
                                   ⟶ applyKont asgnK: setLocal t, value, kont []
                                   ⟶ applyKont []:   done
```

The post-machine is `m` with its control word moved and one local rebound, which is exactly
the pair of transports on file: `StateOk_reCtl` and `StateOk_setLocal`.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The three steps, as `stepFn` facts -/

/-- Step 1: the assignment pushes `asgnK` and turns to the right-hand side. `rfl`. -/
theorem stepFn_vasgn (m : Machine) (t x : String) :
    Interp.stepFn (evalFrom m (.vasgn .lvar t (.var .lvar x)))
      = .next (reCtl m (.eval (.var .lvar x)) [.asgnK .lvar t]) := rfl

/-- Step 2: the local is read. Not `rfl` — `getLocal` is read at the redirected machine. -/
theorem stepFn_var_kont (m : Machine) (t x : String) :
    Interp.stepFn (reCtl m (.eval (.var .lvar x)) [.asgnK .lvar t])
      = .next (reCtl m (.value (m.getLocal x)) [.asgnK .lvar t]) := by
  simp only [Interp.stepFn, Interp.evalExpr, Interp.withCtl, reCtl, getLocal_reCtl]

/-- Step 3: `asgnK` pops, writes the local, and delivers the value to the empty
continuation. `rfl`. -/
theorem stepFn_asgnK (m : Machine) (t : String) (v : Value) :
    Interp.stepFn (reCtl m (.value v) [.asgnK .lvar t])
      = .next (reCtl ((reCtl m (.value v) []).setLocal t v) (.value v) []) := rfl

/-! ## The rung -/

theorem Sem.Judge.vasgnAlias : Obl.Judge.vasgnAlias := by
  intro κ Γ I t x σ τ _htemp hget hstrip hcap hctx m hm v m' h
  -- The value read is `m.getLocal x`, and the run is the four steps above.
  obtain ⟨rfl, rfl⟩ :=
    evals_four (stepFn_vasgn m t x) (stepFn_var_kont m t x)
      (stepFn_asgnK m t (m.getLocal x)) h
  -- `M` is `m` with its control word moved; the write happens there.
  let M : Machine := reCtl m (.value (m.getLocal x)) []
  have hM : M = reCtl m (.value (m.getLocal x)) [] := rfl
  have hMok : StateOk κ Γ I M := StateOk_reCtl hm _ _
  -- The value has the type the rule reports, at `M` and then after the write.
  have hdenM : denM τ M (M.getLocal x) := by
    have hd := (hm.env x σ hget).1
    rw [hstrip] at hd
    rw [hM]
    simpa using denM_reCtl.mpr hd
  have hgetM : M.getLocal x = m.getLocal x := by rw [hM]; simp
  rw [hgetM] at hdenM
  refine ⟨?_, ?_, ?_⟩
  · -- Frame balance: neither the control word nor the write touches the stack.
    show ((M.setLocal t (m.getLocal x)).stack) = m.stack
    rw [setLocal_stack, hM]
  · -- The value's type, transported across the write by `capStale`.
    exact denM_reCtl.mpr (denM_setLocal hdenM hcap hdenM)
  · -- Conformance, by the two transports.
    refine StateOk_reCtl (StateOk_setLocal hMok hdenM hcap hctx rfl ?_) _ _
    -- The alias the rule records: `t` now holds what `x` holds. When `x` and `t` are the
    -- same name that is the value just written; otherwise `x` was not touched.
    intro y ρ hy
    cases hy
    by_cases hxt : x = t
    · subst hxt
      exact (getLocal_setLocal_self M x (m.getLocal x) hMok.frameInRange.2).symm
    · rw [getLocal_setLocal_ne M t (m.getLocal x) hxt, hgetM]

#print axioms Sem.Judge.vasgnAlias

end Ratchet.Denote
