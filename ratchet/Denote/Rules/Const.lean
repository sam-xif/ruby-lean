import Denote.Rules.Core
import Denote.Rules.Regexp
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Const.lean` — the three `.const` rules that name a class

`Judge.constCls`, `Judge.constBuiltin` and `Judge.constExc` are one expression head
(`Expr.const n`), one conclusion (`Ty.clsOf n`) and three different reasons to believe the
name is a class: the program's own class table, `BuiltinCls`, `ExcCls`. So they are one rung
three times, and the shared half is the interesting one.

**A leaf rung with a scope problem.** `evalExpr`'s `.const` arm answers in one step, like
`self'` and `@x`, so `evals_pure` inverts it. But *which* value it answers with is CRuby's
two-phase rule — the lexical phase over the current frame's `cref` first, the inheritance
phase from its `defmod` second — while `denM (.clsOf n)`'s probe (`isClassRefNamed`, hence
`classNamed?`) resolves the name through the **toplevel** constant table and nothing else.
Nothing in `Ctx` records where the frame is standing, so nothing in `StateOk` made those two
the same value, and the obligations were not derivable. That is `Denote/Sem/notes.md`'s stall
point (1) — a missing conformance component — and the component is `ConstScopeOk`
(`Denote/Sem/State.lean`): the current scope resolves constants exactly as the toplevel table
does. `Denote/Sanity.lean` exhibits it at the real booted machine.

**What each rule then spends.**

* `constCls` spends `ClassesOk`: the class table entry for `n` is a real class of that name,
  which is `classNamed? m.heap n = some k` — and that *is* `constLookup m.heap n = some (.ref
  k)` with a class payload, which is what the conclusion needs.
* `constBuiltin` and `constExc` have no table entry to spend, so they spend `CoreOk.coreNamed`
  instead: a name on the fixed twenty-two-element list is, *if bound at all*, bound to a class.
  The "if bound at all" is not hedging — the model has no `IOError`, so `ExcCls.ioError` is a
  case with no value to type, and the rung closes it by having nothing to prove rather than by
  a fact about the heap.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## Inverting a run that never returns

Two shapes the `.const` head can take when the name resolves to nothing, and neither produces
a value — so the obligation's hypothesis is unsatisfiable and the case costs nothing. The
`.unsupported` half is `evals_of_unsupported` (`Denote/Rules/Regexp.lean`); the raise half
needs its own two-step inversion, and it is worth having by name for the same reason: it is
the shape *every* `Interp.raiseErr` at an empty continuation takes on this ladder. -/

/-- One more step after the run has begun, landing on `.uncaught`: no run returns a value. -/
theorem evals_of_uncaught {m : Machine} {e : Ratchet.Expr} {m₁ m₂ : Machine} {exc v : Value}
    {m' : Machine}
    (h1 : Interp.stepFn (evalFrom m e) = .next m₁)
    (h2 : Interp.stepFn m₁ = .uncaught exc m₂)
    (h : Evals m e v m') : False := by
  obtain ⟨fuel, hrun⟩ := h
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | 1 => simp only [run_succ, h1, run_zero] at hrun; exact absurd hrun (by simp)
  | fuel + 2 => simp only [run_succ, h1, h2] at hrun; exact absurd hrun (by simp)

/-- **A raise at the empty continuation escapes.** `raiseErr` allocates the exception and sets
`ctl := .jump (.raiseJ …)`; `unwind` at `kont = []` answers `.uncaught` outright. -/
theorem stepFn_raiseErr_nil (m : Machine) (cls : ObjId) (msg : String) (hk : m.kont = []) :
    Interp.stepFn (Interp.raiseErr m cls msg)
      = .uncaught (Builtins.allocExc m cls msg).1 (Interp.raiseErr m cls msg) := by
  have hctl : (Interp.raiseErr m cls msg).ctl
      = Ctl.jump (Jump.raiseJ (Builtins.allocExc m cls msg).1) := rfl
  have hkont : (Interp.raiseErr m cls msg).kont = [] := by rw [← hk]; rfl
  simp only [Interp.stepFn, hctl, Interp.unwind, hkont]

/-! ## The step -/

/-- One step from `.const n`: the value is whatever the machine's own two-phase resolution
answers, and nothing but `ctl` moves. `constResolveAt` (`Denote/Sem/State.lean`) is that
resolution transcribed, which is what makes this a rewrite rather than a case split. -/
theorem stepFn_const {m : Machine} {n : String} {v : Value}
    (h : constResolveAt m n = some v) :
    Interp.stepFn (evalFrom m (.const n)) = .next (reCtl m (.value v) []) := by
  have h1 : evalFrom m (.const n) = reCtl m (.eval (.const n)) [] := rfl
  rw [h1]
  simp only [Interp.stepFn, Interp.evalExpr, Interp.withCtl, currentFrame_reCtl, heap_reCtl]
  rw [show (Option.orElse (List.firstM (fun c => constOwn m.heap c n) m.currentFrame.cref)
        (fun _ => constLookupFrom m.heap m.currentFrame.defmod n)) = some v from h]

/-! ## From "the name is a class" to the conclusion -/

/-- `classNamed?`'s two halves, spelled out: the name resolves to a reference, and that
reference carries a class payload. Both directions are needed — the rung gets `classNamed?`
from `ClassesOk` and needs `constLookup` to feed `ConstScopeOk`, and then gets `constLookup`
back from the machine and needs `classNamed?` to feed `isClassRefNamed`. -/
theorem constLookup_of_classNamed {h : Heap} {n : String} {k : ObjId}
    (hc : classNamed? h n = some k) : constLookup h n = some (.ref k) := by
  unfold classNamed? at hc
  cases hl : constLookup h n with
  | none => simp [hl] at hc
  | some w =>
    cases w with
    | ref o =>
      simp only [hl] at hc
      split at hc
      · cases hc; rfl
      · simp at hc
    | _ => simp [hl] at hc

theorem classNamed?_of_constLookup {h : Heap} {n : String} {o : ObjId}
    (hl : constLookup h n = some (.ref o)) (hp : (h.classPayload? o).isSome = true) :
    classNamed? h n = some o := by
  simp [classNamed?, hl, hp]

/-- The conclusion of all three rules, from the one fact they each establish differently. -/
theorem denM_clsOf_of_classNamed {m : Machine} {n : String} {k : ObjId}
    (hc : classNamed? m.heap n = some k) : denM (.clsOf n) m (.ref k) := by
  simp only [denM, isClassRefNamed, hc, beq_self_eq_true]

/-- **A name that resolves to nothing produces no value.** `evalExpr`'s `.const` miss branch
either gates (`crubyToplevelConstants`/`crubyStdlibConstants` — a constant CRuby has and the
model does not, which must not answer `nil`) or raises `NameError`, and neither reaches a
`.value`.

This is what makes `Judge.constExc` at `"IOError"` cost nothing: the model has no `IOError`
class, so there is no value for the rule to be wrong about. -/
theorem const_miss_no_value {m : Machine} {n : String} {v : Value} {m' : Machine}
    (hr : constResolveAt m n = none) (h : Evals m (.const n) v m') : False := by
  have h1 : evalFrom m (.const n) = reCtl m (.eval (.const n)) [] := rfl
  have hres : (Option.orElse (List.firstM (fun c => constOwn m.heap c n) m.currentFrame.cref)
      (fun _ => constLookupFrom m.heap m.currentFrame.defmod n)) = none := hr
  by_cases hg : (crubyToplevelConstants.contains n || crubyStdlibConstants.contains n) = true
  · refine evals_of_unsupported (r := s!"unmodeled constant {n}") ?_ h
    rw [h1]
    simp only [Interp.stepFn, Interp.evalExpr, currentFrame_reCtl, heap_reCtl]
    rw [hres]
    simp only [hg, if_pos]
  · simp only [Bool.not_eq_true] at hg
    obtain ⟨msg, hstep⟩ : ∃ msg, Interp.stepFn (evalFrom m (.const n)) =
        .next (Interp.raiseErr (reCtl m (.eval (.const n)) []) Boot.nameErrorId msg) := by
      rw [h1]
      simp only [Interp.stepFn, Interp.evalExpr, currentFrame_reCtl]
      rw [hres]
      simp only [hg, if_neg, Bool.false_eq_true, not_false_eq_true]
      exact ⟨_, rfl⟩
    exact evals_of_uncaught hstep (stepFn_raiseErr_nil _ _ _ rfl) h

/-- **The shared rung.** Every `.const` rule that concludes `.clsOf n` reduces to this: at a
conformant machine, if the name resolves to a class in the toplevel table then the run's value
is that class object and the machine is the one it started from.

Stated over `classNamed?` rather than over any one rule's premise, so the three rungs below
differ only in how they produce it. -/
theorem semJudge_const_clsOf {κ : Ctx} {Γ : Env} {I : Ty} {n : String}
    (hname : ∀ m : Machine, StateOk κ Γ I m → ∀ v, constResolveAt m n = some v →
      ∃ k, classNamed? m.heap n = some k ∧ v = .ref k) :
    SemJudge κ Γ I (.const n) (.clsOf n) (κ.afterStmt (.const n) (.clsOf n)) Γ I := by
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  -- The machine answered *something*, so resolution succeeded; that is where the value is.
  cases hr : constResolveAt m n with
  | none => exact absurd hev (const_miss_no_value hr)
  | some w =>
    obtain ⟨k, hk, rfl⟩ := hname m hm w hr
    obtain ⟨rfl, rfl⟩ := evals_pure (stepFn_const hr) hev
    exact ⟨Framed_reCtl _ _ _, denM_reCtl.mpr (denM_clsOf_of_classNamed hk), StateOk_reCtl hm _ _, StateOk_reCtl hm _ _⟩


/-! ## The three rules

Each supplies `semJudge_const_clsOf`'s one hypothesis, and nothing else. -/

/-- The class table's key *is* the entry's name — `clsGet?` is a `find?` on exactly that
field — which is what lets `ClassesOk` (stated over `c.name`) answer a question about `n`. -/
theorem clsGet?_name {C : CTable} {n : String} {c : Cls} (h : clsGet? C n = some c) :
    c ∈ C ∧ c.name = n :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem mem_coreClsNames_of_builtin {n : String} (h : BuiltinCls n) : n ∈ coreClsNames := by
  cases h <;> simp [coreClsNames]

theorem mem_coreClsNames_of_exc {n : String} (h : ExcCls n) : n ∈ coreClsNames := by
  cases h <;> simp [coreClsNames]

/-- **A declared class.** `ClassesOk` says the table entry names a real class; `ConstScopeOk`
says the machine finds that one. -/
theorem Sem.Judge.constCls : Obl.Judge.constCls := by
  intro κ Γ I n c hcls _
  refine semJudge_const_clsOf (fun m hm v hres => ?_)
  obtain ⟨hmem, hname⟩ := clsGet?_name hcls
  obtain ⟨k, hk, _⟩ := hm.classes c hmem
  rw [hname] at hk
  refine ⟨k, hk, ?_⟩
  have := hm.constScope n
  rw [hres, constLookup_of_classNamed hk] at this
  exact Option.some.inj this

/-- **A builtin class.** No table entry to spend, so `CoreOk.coreNamed` does the work: a name
on the fixed list is bound to a class if it is bound at all, and the machine produced a value,
so it is bound. -/
theorem Sem.Judge.constBuiltin : Obl.Judge.constBuiltin := by
  intro κ Γ I n hb _ _
  refine semJudge_const_clsOf (fun m hm v hres => ?_)
  have hl : constLookup m.heap n = some v := by rw [← hm.constScope n]; exact hres
  obtain ⟨o, rfl, hp⟩ := hm.core.coreNamed n (mem_coreClsNames_of_builtin hb) v hl
  exact ⟨o, classNamed?_of_constLookup hl hp, rfl⟩

/-- **An exception class.** Identical to `constBuiltin`, and the reason the two are separate
rules is `Ratchet/Judge.lean`'s, not this file's. The one thing worth noting is the case that
is *not* here: `ExcCls.ioError` names a class the model does not have, and it is discharged by
`const_miss_no_value` above — no value, nothing to be wrong about. -/
theorem Sem.Judge.constExc : Obl.Judge.constExc := by
  intro κ Γ I n he _ _
  refine semJudge_const_clsOf (fun m hm v hres => ?_)
  have hl : constLookup m.heap n = some v := by rw [← hm.constScope n]; exact hres
  obtain ⟨o, rfl, hp⟩ := hm.core.coreNamed n (mem_coreClsNames_of_exc he) v hl
  exact ⟨o, classNamed?_of_constLookup hl hp, rfl⟩

/-- **A constant the context types.** The rung that made `ConstsOk` change shape: the
component now quantifies over `constGet?` — the function the rule's premise is about — rather
than over `Ctx.consts`' entries, so it hands the rung exactly the resolved value and its type.
Under the old entry-wise form there was nothing to connect the *absolute path* the table is
keyed by (`"::A::X"`) to the *source name* the machine resolves (`X`); see the component's
docstring.

Note this rung spends no `ConstScopeOk`: the value it needs is the one the machine produced,
and `ConstsOk` is now stated at the machine's own resolution. -/
theorem Sem.Judge.constEnv : Obl.Judge.constEnv := by
  intro κ Γ I n τ hget
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' hev
  obtain ⟨w, hres, hden⟩ := hm.consts n τ hget
  obtain ⟨rfl, rfl⟩ := evals_pure (stepFn_const hres) hev
  exact ⟨Framed_reCtl _ _ _, denM_reCtl.mpr hden, StateOk_reCtl hm _ _, StateOk_reCtl hm _ _⟩

#print axioms Sem.Judge.constCls
#print axioms Sem.Judge.constBuiltin
#print axioms Sem.Judge.constExc
#print axioms Sem.Judge.constEnv

end Ratchet.Denote
