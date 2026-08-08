import RubyCore.Heap

/-!
# Heap facts for `TableOk` under `defineMethod`

`docs/semantics/static-soundness-poc.md` §8.3. P1b's remaining obligation: a
user `def` mutates the method table (`Interp.lean:2615`), so `Inv`'s `TableOk`
conjunct — "the tabulated `Integer` builtins still resolve" — has to survive it.

`TableOk` reaches the heap through exactly two functions, `lookup` and
`ancestors`, so the obligation decomposes into a chain:

1. **`shape_defineMethod`** (here) — `defineMethod` leaves every payload field
   *except* `methods` alone. This is what makes the rest possible: `ancestors`
   reads only `prepends`/`includes`/`superclass`.
2. **`ancestors` congruence** under (1) — *not yet proved*. Needs a fuel
   induction over `ancestors.go` **and** a second over `modAncestors.go`
   (`Heap.lean:416`, `Heap.lean:431`), since the chain walk splices included
   modules.
3. **`lookup` congruence** given (2) plus **name-disjointness** — *not yet
   proved*. The disjointness is the cheap route: at every class in the chain,
   `methods.find? (·.1 == m)` is unaffected by prepending an entry named
   `name ≠ m`, which is `find?_filter_ne` (already proved in
   `StaticSoundness.lean`). It avoids having to reason about *where* in the chain
   resolution happens, which the alternative — "the resolving class precedes
   `owner`" — would require.
4. `IntBuiltinResolves` preservation, then `TableOk`, then the `def` case of
   `step_ok`.

The fragment supplies (3)'s side condition for free: it can forbid `def`ining a
name in `builtinSig`, which is syntactic.

**The alternative considered and rejected.** State `check_sound` from a machine
where the `def`s are already installed (`sound_from`), discharging the setup
per-program by `native_decide` — the same split P1d needs for sigs. That dodges
this chain entirely but weakens the headline claim for every method-bearing
program, and these lemmas are reusable by any future heap-mutating step, so the
chain is worth paying for once.
-/

namespace RubyCore
namespace Proof

/-! ## Array facts, `Object` flavour

The `Frame` versions live in `StaticSoundness.lean`. They are stated separately
rather than generalized over the element type because both need
`Inhabited`-specific `default` reasoning and the shared form was not shorter.
-/

theorem objs_getD_set!_ne (a : Array Object) (i j : Nat) (o : Object) (h : j ≠ i) :
    (a.set! i o).getD j default = a.getD j default := by
  have hsz : (a.set! i o).size = a.size := by simp [Array.set!]
  by_cases hj : j < a.size
  · simp only [Array.getD]
    rw [dif_pos (hsz ▸ hj), dif_pos hj]
    exact Array.getElem_setIfInBounds_ne hj (Ne.symm h)
  · simp only [Array.getD]
    rw [dif_neg (hsz ▸ hj), dif_neg hj]

/-- Out of bounds, `Heap.get` yields `default`, whose payload is `.none` — so
    there is no class there. Needed to discharge the case where `defineMethod`'s
    target does not exist, which `classPayload? = some _` rules out. -/
theorem classPayload?_oob (h : Heap) (k : ObjId) (hb : ¬ k < h.objs.size) :
    h.classPayload? k = none := by
  unfold Heap.classPayload? Heap.get
  simp [Array.getD, hb]
  rfl

/-! ## Step 1 of the chain -/

/-- The payload fields `ancestors`/`modAncestors` actually read. -/
def clsShape (c : ClassPayload) : List ObjId × List ObjId × Option ObjId :=
  (c.prepends, c.includes, c.superclass)

/-- **`defineMethod` changes `methods` and nothing else.**

    Proof note, because it cost time: `Heap.set` is `Array.set!`, so the `k = cls`
    case needs the in-bounds fact, which `classPayload? k = some c` supplies via
    `classPayload?_oob`; and the `k ≠ cls` case is `objs_getD_set!_ne`. Going
    through `simp [Heap.set]` without splitting on the bound leaves an
    irreducible `if k < size` in the goal. -/
theorem shape_defineMethod (h : Heap) (cls k : ObjId) (name : String)
    (md : MethodDef) :
    ((defineMethod h cls name md).classPayload? k).map clsShape
      = (h.classPayload? k).map clsShape := by
  unfold defineMethod
  split
  · rename_i c hc
    by_cases hk : k = cls
    · subst hk
      simp only [Heap.setClassPayload, Heap.classPayload?, Heap.get, Heap.set]
      by_cases hb : k < h.objs.size
      · simp [Array.getD, hb, Array.set!, clsShape]
        unfold Heap.classPayload? Heap.get at hc
        simp [Array.getD, hb] at hc
        split at hc <;> simp_all [clsShape]
      · rw [classPayload?_oob h k hb] at hc; exact absurd hc (by simp)
    · simp only [Heap.setClassPayload, Heap.classPayload?, Heap.get, Heap.set]
      rw [objs_getD_set!_ne _ _ _ _ hk]
  · rfl

end Proof
end RubyCore
