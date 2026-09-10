import Denote.Rules.Alloc
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Regexp.lean` — the second allocating literal

`Judge.regexpLit` is `Judge.strLit`'s shape (`Denote/Rules/Lit.lean`) with one new feature:
`evalExpr`'s arm is **partial**.

```
| .regexpLit src opts =>
  match Rx.parse src opts with
  | .error e => .unsupported e
  | .ok _ => … one allocation, then the value
```

So the rung has two cases and only one of them allocates:

* **A pattern the model's regexp engine does not accept** gates as `.unsupported`, which is
  not a `.value` — so the obligation's hypothesis `Evals m e v m'` is *unsatisfiable* and the
  case closes with no claim about the type at all. `evals_of_unsupported` is that
  contradiction, and it is worth having by name: it is the shape every `.unsupported` gate in
  the model takes on this ladder, and it is why a gated construct costs a rung nothing.
  (It is also exactly the partial-correctness reading `Evals`' docstring argues for — a run
  that gates imposes nothing.)
* **A pattern it accepts** pushes one object and answers `.ref` at the fresh id, which is
  `ext_push` and then `StateOk_ext`, precisely as `strLit`.

The one thing that had to move was `CoreOk`: the rule concludes `.cls "Regexp"`, whose
denotation resolves the *name* `Regexp` through the heap, and a conformant machine was not
required to have such a class. Three clauses added (`regexpNamed`/`regexpSelf`/`regexpBasic`),
which is the growth `CoreOk`'s own docstring predicted ("this will grow … each will want its
own row here"), and `Denote/Sanity.lean`'s `coreOkB` measures them at the booted heap.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **A gated step imposes nothing.** If evaluating `e` from `m` steps straight to
`.unsupported`, no run of it returns a value. -/
theorem evals_of_unsupported {m : Machine} {e : Ratchet.Expr} {r : String} {v : Value}
    {m' : Machine} (hstep : Interp.stepFn (evalFrom m e) = .unsupported r)
    (h : Evals m e v m') : False := by
  obtain ⟨fuel, hrun⟩ := h
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | fuel + 1 => rw [run_succ, hstep] at hrun; exact absurd hrun (by simp)

/-- The object a regexp literal allocates: the same payload `Regexp.new` builds. -/
def rxObj (src : String) (opts : Nat) : Object :=
  { klass := Boot.regexpId, payload := .regexp src opts }

/-- One `stepFn` step from an accepted regexp literal. -/
theorem stepFn_regexp {src : String} {opts : Nat} (m : Machine) {rx : Rx.Regex}
    (hp : Rx.parse src opts = .ok rx) :
    Interp.stepFn (evalFrom m (.regexpLit src opts)) =
      .next (reCtl { m with heap := pushHeap m.heap (rxObj src opts) }
        (.value (.ref m.heap.objs.size)) []) := by
  simp only [evalFrom, toRuby, Interp.stepFn, Interp.evalExpr, hp, Interp.withCtl, reCtl,
    pushHeap, rxObj, Heap.alloc]

/-- The gated step, for the patterns `Rx.parse` rejects. -/
theorem stepFn_regexp_gated {src : String} {opts : Nat} (m : Machine) {e : String}
    (hp : Rx.parse src opts = .error e) :
    Interp.stepFn (evalFrom m (.regexpLit src opts)) = .unsupported e := by
  simp only [evalFrom, toRuby, Interp.stepFn, Interp.evalExpr, hp]

theorem Sem.Judge.regexpLit : Obl.Judge.regexpLit := by
  intro κ Γ I src opts
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' h
  cases hp : Rx.parse src opts with
  | error e => exact absurd h (fun h => evals_of_unsupported (stepFn_regexp_gated m hp) h)
  | ok rx =>
    obtain ⟨rfl, rfl⟩ := evals_pure (stepFn_regexp m hp) h
    have hext : Ext m (reCtl { m with heap := pushHeap m.heap (rxObj src opts) }
        (.value (.ref m.heap.objs.size)) []) :=
      (ext_push (m := m) (rxObj src opts) hm.sat hm.core.basicSelf
        (fun c => by simp [rxObj]) rfl rfl
        (by simpa [rxObj] using hm.core.regexpBasic)).trans (Ext_toReCtl _ _ _)
    refine ⟨Framed.of_ext hext, ?_, StateOk_ext hm hext, StateOk_ext hm hext⟩
    -- `.ref n` is a `Regexp`: the name still resolves, and the fresh object's ancestor walk
    -- is `Regexp`'s. Same three lines as `strLit`.
    have hanc : ∀ k, ancestors (pushHeap m.heap (rxObj src opts)) k = ancestors m.heap k :=
      Proof.ancestors_congr_grow hext.shapeAgree hext.size hm.sat
    have hcls : classOf (pushHeap m.heap (rxObj src opts)) (.ref m.heap.objs.size)
        = Boot.regexpId := by
      simp [classOf, pushHeap_get_self, rxObj]
    rw [denM, isAName, hext.classNamed?_eq, hm.core.regexpNamed]
    show (ancestors (pushHeap m.heap (rxObj src opts)) _).contains _ = true
    rw [hcls, hanc]
    exact hm.core.regexpSelf

#print axioms Sem.Judge.regexpLit

end Ratchet.Denote
