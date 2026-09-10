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


/-! ### `enterUserMethod`, parked with a **measurement** — it needs hand-splitting, not a budget

The one `frames.push` in the model whose `captured` comes from a **`MethodDef`** rather than a
frame or a closure, which is why L267 added `Sealed`'s third clause. Everything it needs is on
file: `Step.push_meth`/`push_meth'` for the push, and `methodIn_alloc` (`StepSupport.lean`) to
carry the `Sealed.meth` fact across the allocations the body performs first (a keyword bundle
via `appendKwHash`, a rest array via `allocArr`).

**What is not on file is a proof, and the reason is measured rather than guessed.** With the
corrected recipe (peel first, refute through the hypothesis, `hmd` supplied directly) the
closer fixpoint runs **26 minutes and does not finish at 60 000 000 heartbeats**. Memory stays
flat at ~516 MB, so this is search, not a term explosion: ten branch points over a 135-line body
produce dozens of leaves, and two of the closers (`Step.raiseErr`, `Step.allocArr`) are
goal-keyed and therefore expensive *to fail* at each one — item 1 of §The second walk, at a
scale where it dominates.

`RubyCore/Proof/KontFrame.lean` hit exactly this and records the same shape: `enterUserMethod`
is "`split`-bound on a 135-line body with ten branch points and is the one function whose build
cost is measured in minutes". Its resolution was to **hand-split the branch points** so no
search happens at all, which is the approach here too — ~10 explicit `by_cases`/`cases hc :`
peels with one `exact` per leaf. That is deterministic work; it is not a bigger heartbeat
budget, and raising the budget further would only buy a longer wait.

Its first condition is already peeled and correct:
`by_cases h1 : (Interp.classifyFull md.params).isNone = true`, with the `true` branch closing by
`cases hstep` on the `.unsupported`/`.next` constructor mismatch. -/

#print axioms Step.eigenclassOf_go
#print axioms Step.eigenclassOf

end Ratchet.Denote
