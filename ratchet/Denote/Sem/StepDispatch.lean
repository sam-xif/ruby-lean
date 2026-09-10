import Denote.Sem.StepSupport

/-!
# `Denote/Sem/StepDispatch.lean` — stage 2 of the walk: `Interp/Dispatch.lean`

Stage 1 is `StepSupport.lean`. This is the layer above it, in the bottom-up order
`StepEval.lean` records.

`eigenclassOf` is the one with structure: a fuel recursion that walks the superclass chain and,
at each level that has no eigenclass yet, **allocates one and writes the attachee's `eigen`
field**. That is `MCap.push_free_then_set`'s shape — a capture-free `.cls` push (empty method
table) followed by a payload-preserving `set` — and the induction is on the fuel, which is why
`Interp.eigenclassOf` is fuel-bounded rather than `partial` in the first place.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

/-- **`eigenclassOf.go`**, by induction on the fuel. -/
theorem Step.eigenclassOf_go {b : FrameId} :
    ∀ (fuel : Nat) (m : Machine) (o : ObjId), StepInv b m →
      Step b m (Interp.eigenclassOf.go m o fuel).2
  | 0, m, o, h => Step.refl h
  | fuel + 1, m, o, h => by
    rw [Interp.eigenclassOf.go]
    split
    · exact Step.refl h
    · -- compute the metaclass superclass (possibly recursing), then allocate and write
      have hgo : ∀ (m₂ : Machine) (o₂ : ObjId), StepInv b m₂ →
          Step b m₂ (match (m₂.heap.get o₂).payload with
            | .cls c => match c.superclass with
              | some s => Interp.eigenclassOf.go m₂ s fuel
              | none => ((if c.isModule then Boot.moduleId else Boot.classId), m₂)
            | _ => ((m₂.heap.get o₂).klass, m₂)).2 := by
        intro m₂ o₂ h₂
        split
        · split
          · exact Step.eigenclassOf_go fuel m₂ _ h₂
          · exact Step.refl h₂
        · exact Step.refl h₂
      refine Step.heap' (hgo m o h) rfl rfl ?_
      refine MCap.push_free_then_set rfl ?_ rfl
      exact fun _ => capAt_cls_nil rfl rfl

/-- **`eigenclassOf`** itself, at the fuel the model gives it. -/
theorem Step.eigenclassOf {b : FrameId} (m : Machine) (o : ObjId) (h : StepInv b m) :
    Step b m (Interp.eigenclassOf m o).2 := by
  rw [Interp.eigenclassOf]
  exact Step.eigenclassOf_go _ m o h

/-- `eigenclassOf` as a **peel**, for an arm that reaches it after doing something else —
`enterClassBody`'s create path allocates and registers the constant first. -/
theorem Step.eigenclassOf' {b : FrameId} {m mid : Machine} (s : Step b m mid) (o : ObjId) :
    Step b m (Interp.eigenclassOf mid o).2 := s.trans (Step.eigenclassOf mid o s.2)

/-! ### `enterClassBody` — peeled by hand, because `split at h` cannot see these scrutinees

The obstruction that parked this (and `callClosure`, and `enterHandler`) is one thing:
`split at h` peels the chains in `Builtins` — six hundred arms under a single `match` on `bid` —
and fails on the ones in `Interp/`, where the arms are guarded by `let`-bound scrutinees and
helper calls. `Builtins` was the wrong sample to calibrate the tactic on, and `split_ifs` is
Mathlib-only and not in this package.

The technique that works is `cases hc : <scrutinee>` followed by `rw [hc] at hstep` — naming the
scrutinee rather than asking `split` to find it, which is what `FrameLocal.lean` does for
`newImpl_locals` and what closed `doReturn` in stage 1.

Two paths. **Reopen** finds the existing class object and pushes straight away. **Create**
allocates the class (`.cls`, empty method table), registers the constant in the enclosing
namespace (`constSetIn`, a payload-preserving `setClassPayload`), realises the metaclass chain
through `Step.eigenclassOf`, then pushes. Either way the pushed frame's `captured` is
**defaulted**, so `Step.push_free` discharges both of `Sealed.push`'s premises vacuously — one of
the four sites the L266 `Option` made free. -/

/-! **Deprioritised, not blocked.** `enterClassBody` feeds `evalExpr`'s `class`/`module` arms,
whose rules (`classStmt`/`moduleStmt`) belong to the declaration family — so it is *not* on the
path to any of the 26 reachable rules. Its create path is understood (allocate the class,
`constSetIn` the constant, `Step.eigenclassOf'`, then `Step.push_free`) and its two remaining
`rfl`s are heap-shape work against `setClassPayload` nested under `constSetIn`'s own match. The
call family is the reachable prize, so the effort goes there.

The reopen path, for the record, is one line: `Step.push_free h _ rfl` under `Step.withKont'`. -/


#print axioms Step.eigenclassOf_go
#print axioms Step.eigenclassOf

end Ratchet.Denote
