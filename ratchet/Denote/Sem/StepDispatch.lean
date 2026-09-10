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


/-! ### `enterUserMethod` — the `Sealed.meth` push site

The one `frames.push` whose `captured` comes from a **`MethodDef`** rather than a frame or a
closure, which is why L267 added `Sealed`'s third clause. The premise is a heap lookup
(`methodIn`), carried across the allocations the body performs first — a keyword bundle via
`appendKwHash`, a rest array via `allocArr`, a destructuring bind via `destructureBind` — by
`methodIn_alloc`.

**Retried after `destructureBind`**, whose fix applies here too: `rw [f.eq_def]` rather than the
bare name, since the conditional equations of a nested-match definition leave discriminating side
goals that look like unsolved cases. The first branch (`classifyFull`'s gate) is peeled by hand
because `split` will not fire on it; note that `classifyFull` ends `if false then none`, so that
branch is dead code and closes on the `.unsupported`/`.next` constructor mismatch. -/

/-! **Status: one transcription away, with no unknowns left.** Everything it needs is proved —
`Step.push_meth`/`push_meth'` for the push, `methodIn_alloc` for the lookup across its
allocations, `Step.appendKwHash`, `Step.allocArr_eq`, `Step.allocHsh_eq`, and (since it folds
over destructuring sub-parameters) `Step.destructureBind`.

What remains is *not* a proof problem and *not* a budget problem, and three attempts establish
that: with the closer fixpoint it does not finish at 4M heartbeats (~110 s), at 60M (26 min), or
with every closer moved to `_eq` form. Memory stays flat, so it is search — `split at hstep` on a
135-line body with ten branch points, producing goals faster than any closer list can absorb
them. `RubyCore/Proof/KontFrame.lean` reached the same conclusion about the same function and
hand-split it.

So the remaining work is transcribing ~7 conditions as explicit `by_cases`/`cases hc :` peels —
`hasKw`, `arityOk`, the two keyword checks, `fp.rest?`, `fp.kwrest?`, and the `destrs` fold —
with one `exact` per leaf. Mechanical, deterministic, and the conditions are readable off
`Interp/Dispatch.lean`. The first is already peeled here, and `classifyFull` ends
`if false then none`, so that branch is dead code that closes on the constructor mismatch. -/

#print axioms Step.eigenclassOf_go
#print axioms Step.eigenclassOf

end Ratchet.Denote
