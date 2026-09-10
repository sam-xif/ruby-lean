import Denote.Rules.Alloc
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Lit.lean` — the leaf rungs: seven literals, two local reads, one delegation

The first ten rungs of the semantic ratchet (`Denote/Sem/notes.md`). Every one of them is the
same three lines, because every one of them is the same two `stepFn` steps:

```
evalFrom m e   ⟶ evalExpr: .value w   ⟶ applyKont []: .done w
```

`Denote/Rules/Core.lean`'s `evals_pure` does the inversion; what is left per rule is *what
`w` is* and *why it is in the type*. So the interesting content of this file is exactly the
two places where those are not immediate:

* **`Judge.var` and `Judge.varAlias` read `EnvOk`.** The value is `m.getLocal x`, and the
  claim that it is in `τ` is the environment component of conformance — the first rung whose
  proof consumes a `StateOk` field rather than re-establishing it unchanged. `var`'s
  `isAliasTy τ = false` premise is what makes `stripAlias τ` (which is what `EnvOk` states)
  equal to `τ` (which is what the rule concludes); `varAlias` is the complementary case, where
  `EnvOk`'s `stripAlias (.sameAs y τ) = τ` does the same job from the other side. Neither rung
  needs `EnvOk`'s *identity* conjunct — that one is for `Judge.narrowEnvs` later.

* **`Judge.seq` is a delegation, and the delegation is definitional.** `SemJudgeSeq κ Γ I es
  τ Γ' I'` unfolds to `SemJudge κ Γ I (.seq es) τ Γ' I'`, exactly as its docstring says
  (`JudgeSeq` exists so the context can grow *between* statements, which is a fact about
  `JudgeSeq`'s own rules, not about the sequence's meaning). So the rung is the identity, and
  it is worth having on file as such: the ladder counts it, and the reader who expected a
  proof learns instead that the two definitions were deliberately made the same statement.

`Judge.strLit` is **not** here, and its absence is a finding rather than an omission: a
string literal *allocates*, which makes it the first rung whose post-machine differs from its
pre-machine in the heap, and two things `StateOk` and `denM` do not currently supply are
needed to close it. Both are written up as the fourth stall point in
[`../Sem/notes.md`](../Sem/notes.md) and in this clink's entry in `../../implementation-notes.md`.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The pure literals

Each `stepFn` fact below is `rfl`: `toRuby` is the identity on the constructor, `evalExpr`
answers with the value, and nothing in the machine but `ctl` moves. -/

theorem Sem.Judge.intLit : Obl.Judge.intLit := by
  intro κ Γ I n
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  obtain ⟨rfl, rfl⟩ := evals_pure (w := .int n) rfl h
  exact ⟨Framed_reCtl _ _ _, by simp [denM, isIntV], StateOk_reCtl hm _ _, StateOk_reCtl hm _ _⟩

theorem Sem.Judge.fltLit : Obl.Judge.fltLit := by
  intro κ Γ I bits
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  obtain ⟨rfl, rfl⟩ := evals_pure (w := .flt (Float.ofBits bits)) rfl h
  exact ⟨Framed_reCtl _ _ _, by simp [denM, isFltV], StateOk_reCtl hm _ _, StateOk_reCtl hm _ _⟩

theorem Sem.Judge.symLit : Obl.Judge.symLit := by
  intro κ Γ I s
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  obtain ⟨rfl, rfl⟩ := evals_pure (w := .sym s) rfl h
  exact ⟨Framed_reCtl _ _ _, by simp [denM, isSymV], StateOk_reCtl hm _ _, StateOk_reCtl hm _ _⟩

theorem Sem.Judge.truLit : Obl.Judge.truLit := by
  intro κ Γ I
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  obtain ⟨rfl, rfl⟩ := evals_pure (w := .bool true) rfl h
  exact ⟨Framed_reCtl _ _ _, by simp [denM, isBoolV], StateOk_reCtl hm _ _, StateOk_reCtl hm _ _⟩

theorem Sem.Judge.flsLit : Obl.Judge.flsLit := by
  intro κ Γ I
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  obtain ⟨rfl, rfl⟩ := evals_pure (w := .bool false) rfl h
  exact ⟨Framed_reCtl _ _ _, by simp [denM, isBoolV], StateOk_reCtl hm _ _, StateOk_reCtl hm _ _⟩

theorem Sem.Judge.nilLit : Obl.Judge.nilLit := by
  intro κ Γ I
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  obtain ⟨rfl, rfl⟩ := evals_pure (w := .nil) rfl h
  exact ⟨Framed_reCtl _ _ _, by simp [denM, isNilV], StateOk_reCtl hm _ _, StateOk_reCtl hm _ _⟩

/-! ## Reading a local

The one step is `.value (m.getLocal x)` — but at the *redirected* machine, so the `stepFn`
fact is `getLocal_reCtl` rather than `rfl`. -/

theorem stepFn_var (m : Machine) (x : String) :
    Interp.stepFn (evalFrom m (.var .lvar x)) = .next (reCtl m (.value (m.getLocal x)) []) := by
  simp only [evalFrom, toRuby, toRubyVarKind, Interp.stepFn, Interp.evalExpr, Interp.withCtl,
    reCtl, getLocal_reCtl]

theorem Sem.Judge.var : Obl.Judge.var := by
  intro κ Γ I x τ hget halias
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  obtain ⟨rfl, rfl⟩ := evals_pure (stepFn_var m x) h
  refine ⟨Framed_reCtl _ _ _, ?_, StateOk_reCtl hm _ _, StateOk_reCtl hm _ _⟩
  have hden := (hm.env.1 x τ hget).1
  have : stripAlias τ = τ := by
    cases τ <;> simp_all [stripAlias, isAliasTy]
  rw [this] at hden
  simpa using denM_reCtl.mpr hden

theorem Sem.Judge.varAlias : Obl.Judge.varAlias := by
  intro κ Γ I x y τ hget
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  obtain ⟨rfl, rfl⟩ := evals_pure (stepFn_var m x) h
  refine ⟨Framed_reCtl _ _ _, ?_, StateOk_reCtl hm _ _, StateOk_reCtl hm _ _⟩
  have hden := (hm.env.1 x (.sameAs y τ) hget).1
  simp only [stripAlias] at hden
  simpa using denM_reCtl.mpr hden

/-! ## The literal that allocates

`Judge.strLit` was the ratchet's first stall (`Denote/Sem/notes.md` §The fourth stall point).
It is still two `stepFn` steps — but the first of them pushes an object, so the machine the
inversion delivers differs from the starting one in the *heap* and not only in `ctl`. Both
things that were missing are now on file: `StateOk` carries the two heap components the rule
needs (`HeapSaturated`, `CoreOk`), and `StateOk_ext` transports conformance across the push.
What is left here is three lines of arithmetic-free bookkeeping. -/

/-- The object a string literal allocates: `Builtins.allocStr`'s, named so the rung can talk
about it. Unfrozen, no ivars, no eigenclass — which is what makes `ext_push`'s three
hypotheses `rfl`. -/
def strObj (s : String) : Object := { klass := Boot.stringId, payload := .str s }

/-- One `stepFn` step from a string literal: the fresh object is at the old heap's `size`, and
nothing but `ctl` and the heap moves. -/
theorem stepFn_str (m : Machine) (s : String) :
    Interp.stepFn (evalFrom m (.str s)) =
      .next (reCtl { m with heap := pushHeap m.heap (strObj s) }
        (.value (.ref m.heap.objs.size)) []) := rfl

theorem Sem.Judge.strLit : Obl.Judge.strLit := by
  intro κ Γ I s
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  obtain ⟨rfl, rfl⟩ := evals_pure (stepFn_str m s) h
  -- The push is an `Ext`; `StateOk` and the type then both come from that.
  have hext : Ext m (reCtl { m with heap := pushHeap m.heap (strObj s) }
      (.value (.ref m.heap.objs.size)) []) :=
    (ext_push (m := m) (strObj s) hm.sat hm.core.basicSelf
      (fun c => by simp [strObj]) rfl rfl (by simpa [strObj] using hm.core.stringBasic)).trans
      (Ext_toReCtl _ _ _)
  refine ⟨Framed.of_ext hext, ?_, StateOk_ext hm hext, StateOk_ext hm hext⟩
  -- `.ref n` is a `String`: the name still resolves, and the fresh object's ancestor walk is
  -- `String`'s.
  have hanc : ∀ k, ancestors (pushHeap m.heap (strObj s)) k = ancestors m.heap k :=
    Proof.ancestors_congr_grow hext.shapeAgree hext.size hm.sat
  have hcls : classOf (pushHeap m.heap (strObj s)) (.ref m.heap.objs.size) = Boot.stringId := by
    simp [classOf, pushHeap_get_self, strObj]
  rw [denM, isAName, hext.classNamed?_eq, hm.core.stringNamed]
  show (ancestors (pushHeap m.heap (strObj s)) _).contains _ = true
  rw [hcls, hanc]
  exact hm.core.stringSelf

/-! ## The delegation -/

/-- `SemJudgeSeq` *is* `SemJudge` at a `.seq` — see the module docstring. The two plainness
conjuncts differ, and that is the whole of the remaining difference: the sequence's is about
its statements, the expression's is about its own head (`.seq`, which is plain). -/
theorem Sem.Judge.seq : Obl.Judge.seq := by
  intro κ Γ Γ' I I' es τ κ₁ h
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  obtain ⟨hf, hd, hok⟩ := h.2 m hm v m' hev
  -- `Judge.seq` reports its own `κ`, not the sequence's `κ₁`: a `.seq` used as an *expression*
  -- is not a statement of the enclosing sequence, so what it declared does not escape it. Both
  -- conjuncts are therefore the one `SemJudgeSeq` supplies.
  exact ⟨hf, hd, hok, hok⟩

#print axioms Sem.Judge.intLit
#print axioms Sem.Judge.fltLit
#print axioms Sem.Judge.symLit
#print axioms Sem.Judge.truLit
#print axioms Sem.Judge.flsLit
#print axioms Sem.Judge.nilLit
#print axioms Sem.Judge.strLit
#print axioms Sem.Judge.var
#print axioms Sem.Judge.varAlias
#print axioms Sem.Judge.seq

end Ratchet.Denote
