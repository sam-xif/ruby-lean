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
      exact MCap.push_free_then_set rfl (fun _ => capAt_cls_nil rfl rfl) rfl

/-- **`eigenclassOf`** itself, at the fuel the model gives it. -/
theorem Step.eigenclassOf {b : FrameId} (m : Machine) (o : ObjId) (h : StepInv b m) :
    Step b m (Interp.eigenclassOf m o).2 := by
  rw [Interp.eigenclassOf]
  exact Step.eigenclassOf_go _ m o h

/-! ### `enterClassBody`, parked — the third instance of one mechanical obstruction

Its two paths are both *understood*: **reopen** pushes straight away, and **create** allocates
the class (`.cls`, empty method table), registers the constant (`constSetIn`, a
payload-preserving `setClassPayload`), realises the metaclass chain through `Step.eigenclassOf`
above, then pushes — with the pushed frame's `captured` **defaulted**, so `Step.push_free`
discharges both of `Sealed.push`'s premises vacuously.

What blocks it is what blocked `callClosure` and `enterHandler`: `split at hstep` cannot peel
the leading `match constOwn …`, so the closer fixpoint guesses instead of peeling and times out
(measured: 2 000 000 heartbeats, 47 s). All three need the same treatment — the conditions
peeled by hand, as `FrameLocal.lean` does for `newImpl_locals` — and that is a mechanical batch
rather than three separate problems.

**Worth naming as a pattern before the next attempt**, since it has now cost three lemmas: in
this interpreter, `split at h` peels the `match`/`ite` chains in `Builtins` (where the six
hundred arms are a single `match` on `bid`) and fails on the ones in `Interp/`, where the arms
are guarded by `let`-bound scrutinees and helper calls. `Builtins` was the wrong sample to
calibrate the tactic on. -/

#print axioms Step.eigenclassOf_go
#print axioms Step.eigenclassOf

end Ratchet.Denote
