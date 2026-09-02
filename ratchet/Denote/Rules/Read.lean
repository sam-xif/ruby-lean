import Denote.Rules.Core
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Read.lean` — the two reads that are not locals: `self` and `@x`

Two more leaf rungs, in the sense `Denote/Rules/Lit.lean` establishes: `evalExpr` answers in
one step with a value read out of the machine, and the whole content of the rung is *which
`StateOk` component says that value is in the type*.

* **`Judge.selfExpr`** spends `SelfTyOk`, and spends nothing else. `κ.selfTy = some σ` is both
  the rule's premise and the component's non-trivial case, so the rung is the component.

* **`Judge.ivarRead`** spends `SelfSpineOk`, and it is the rung that made that component say
  something it did not previously say. The rule's type is `(ivarGet? I x).getD .nilT`, so it
  has two cases, and only the first was supported:

  - `ivarGet? I x = some σ` — the spine mentions `@x`, and `denSpine` gives `denM σ` of the
    value read. `denSpineFrom_get` is that projection, one induction over the spine.
  - `ivarGet? I x = none` — the spine does not mention `@x`, and the rule answers `.nilT`,
    whose denotation is `isNilV v = true`. **Nothing made that true.** `denSpine` is a
    *lower* bound — `Denote/Den.lean` says so of `denM`'s `inst` arm in as many words ("ivars
    the type does not mention are unconstrained") — so a conformant machine could have `@x`
    holding `7` with `I = .ivar0`, and the rule would type `@x` as `nil`.

  This is `Denote/Sem/notes.md`'s stall point (1) — a missing `StateOk` component, not a
  missing lemma — and `Judge.ivarRead`'s own docstring had already named the invariant it
  needs: *"the default is sound only because the spine is **complete** — every ivar the object
  has ever been given a value for appears in it"*. `SelfSpineOk` now says exactly that
  (`Denote/Sem/State.lean`), and this rung is where the second half is spent.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## `self` -/

/-- One step from `self'`: the value is the current frame's `self`, and nothing but `ctl`
moves. The frame array and the frame stack are untouched by `evalFrom`, so
`(evalFrom m e).currentFrame` is `m.currentFrame` definitionally and this is `rfl`. -/
theorem stepFn_self (m : Machine) :
    Interp.stepFn (evalFrom m .self') = .next (reCtl m (.value m.currentFrame.self) []) := rfl

theorem Sem.Judge.selfExpr : Obl.Judge.selfExpr := by
  intro κ Γ I σ hself
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  obtain ⟨rfl, rfl⟩ := evals_pure (stepFn_self m) h
  refine ⟨Framed_reCtl _ _ _, ?_, StateOk_reCtl hm _ _⟩
  have hden : denM σ m m.currentFrame.self := by
    have := hm.selfTy; unfold SelfTyOk at this; rw [hself] at this; exact this
  simpa using denM_reCtl.mpr hden

/-! ## `@x` -/

/-- **The spine projection**, at the accumulator `denSpineFrom` threads: a spine that resolves
`x` types what `x` reads, *provided `x` is not already shadowed*. The side condition is what
makes the induction go through — descending past an entry keyed `n` adds `n` to `seen`, and
`ivarGet?` walking past that same entry is exactly the case `n ≠ x`, so the invariant is
maintained. (`Denote/Sem/notes.md` §The tenth stall point for why the accumulator exists.) -/
theorem denSpineFrom_get : ∀ (I : Ty) {x : String} {σ : Ty} {m : Machine} {g : String → Value}
    {seen : List String}, x ∉ seen → ivarGet? I x = some σ →
    denSpineFrom seen I m g → denM σ m (g x)
  | .ivarCons n τ rest, x, σ, m, g, seen, hns, hget, hden => by
    rw [denSpineFrom] at hden
    simp only [ivarGet?] at hget
    by_cases hn : n = x
    · subst hn
      simp only [beq_self_eq_true, if_pos] at hget
      cases hget
      exact hden.1.resolve_left hns
    · have hb : (n == x) = false := by simpa using hn
      rw [hb, if_neg (by simp)] at hget
      exact denSpineFrom_get rest (by simp [hns, Ne.symm hn]) hget hden.2
  | .ivar0, _, _, _, _, _, _, hget, _ => by simp [ivarGet?] at hget
  | .int, _, _, _, _, _, _, hget, _ | .float, _, _, _, _, _, _, hget, _ | .bool, _, _, _, _, _, _, hget, _
  | .nilT, _, _, _, _, _, _, hget, _ | .sym, _, _, _, _, _, _, hget, _ | .any, _, _, _, _, _, _, hget, _
  | .never, _, _, _, _, _, _, hget, _ | .cls _, _, _, _, _, _, _, hget, _ | .clsOf _, _, _, _, _, _, _, hget, _
  | .nilable _, _, _, _, _, _, _, hget, _ | .arrayOf _, _, _, _, _, _, _, hget, _
  | .hashOf _ _, _, _, _, _, _, _, hget, _ | .union _ _, _, _, _, _, _, _, hget, _
  | .arrow0 _, _, _, _, _, _, _, hget, _ | .arrowCons _ _, _, _, _, _, _, _, hget, _
  | .inst _ _, _, _, _, _, _, _, hget, _ | .clos _ _ _, _, _, _, _, _, _, hget, _
  | .sameAs _ _, _, _, _, _, _, _, hget, _ => by simp [ivarGet?] at hget

/-- One step from `@x`: the value is `ivarOf` at `self`. `evalExpr`'s `.ivar` arm splits on
`self` being a reference; `ivarOf` (`Denote/Val.lean`) is that same split, so the two agree by
cases with no arithmetic. -/
theorem stepFn_ivar (m : Machine) (x : String) :
    Interp.stepFn (evalFrom m (.var .ivar x)) =
      .next (reCtl m (.value (ivarOf m.heap m.currentFrame.self x)) []) := by
  have h1 : evalFrom m (.var .ivar x) = reCtl m (.eval (.var .ivar x)) [] := rfl
  rw [h1]
  simp only [Interp.stepFn, Interp.evalExpr, Interp.withCtl, currentFrame_reCtl, ivarOf]
  cases hs : m.currentFrame.self with
  | ref o =>
    cases hf : ((m.heap.get o).ivars.find? (fun p => p.1 == x)) with
    | none => simp [hf]
    | some p => simp [hf]
  | _ => rfl

theorem Sem.Judge.ivarRead : Obl.Judge.ivarRead := by
  intro κ Γ I x
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  obtain ⟨rfl, rfl⟩ := evals_pure (stepFn_ivar m x) h
  refine ⟨Framed_reCtl _ _ _, ?_, StateOk_reCtl hm _ _⟩
  have hspine := hm.selfSpine
  unfold SelfSpineOk at hspine
  refine denM_reCtl.mpr ?_
  cases hget : ivarGet? I x with
  | some σ =>
    simpa [hget] using denSpineFrom_get I (by simp) hget hspine.1
  | none =>
    -- The spine is silent about `@x`, and completeness is what makes the rule's `.nilT` true.
    rw [hspine.2 x hget]
    simp [denM, isNilV]

#print axioms Sem.Judge.selfExpr
#print axioms Sem.Judge.ivarRead

end Ratchet.Denote
