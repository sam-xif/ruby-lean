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
2. **`ancestors` congruence** under (1) — a fuel induction over `ancestors.go`
   **and** a second over `modAncestors.go` (`Heap.lean:416`, `Heap.lean:431`),
   since the chain walk splices included modules.
3. **`lookup` congruence** given (2) plus **name-disjointness**. Disjointness is
   the cheap route: at every class in the chain, `methods.find? (·.1 == m)` is
   unaffected by prepending an entry named `name ≠ m` (`find?_filter_ne`). It
   avoids reasoning about *where* in the chain resolution lands, which the
   alternative — "the resolving class precedes `owner`" — would require.
4. `IntBuiltinResolves` and `TableOk` preservation, in
   `BuiltinConformance.lean` and `StaticSoundness.lean` respectively, since they
   need `Interp` and the checker.

All of 1–3 are proved here.

The fragment supplies (3)'s side condition for free: it can forbid `def`ining a
name the declaration table names, which is syntactic (`Types.declaresName`).

**The alternative, rejected twice over.** State `check_sound` from a machine with
the `def`s already installed, discharging setup per-program by `native_decide`.
It dodges this chain entirely, but it weakens the headline claim for every
method-bearing program *and* it violates the standing rule of §8.4 / L94 — no
`native_decide` above a per-program leaf, because it puts the Lean compiler in
the trust base. These lemmas are reusable by any future heap-mutating step, so
the chain is worth paying for once.
-/

namespace RubyCore
namespace Proof

/-! ## Array facts, `Object` flavour

The `Frame` versions live in `StaticSoundness.lean`. They are stated separately
rather than generalized over the element type because both need
`Inhabited`-specific `default` reasoning and the shared form was not shorter.
`find?_filter_ne` lives here rather than there because both consumers need it.
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

/-- The companion of `objs_getD_set!_ne` at the written index. Needed by F1b's
    `Static.plainRecv_defineMethod`, which has to read the payload `defineMethod`
    just wrote rather than only the ones it left alone. -/
theorem objs_getD_set!_self (a : Array Object) (i : Nat) (o : Object) (h : i < a.size) :
    (a.set! i o).getD i default = o := by
  simp [Array.getD, h]

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

/-! ## Steps 2 and 3 of the chain -/

abbrev ShapeAgree (h h' : Heap) : Prop :=
  ∀ k, (h'.classPayload? k).map clsShape = (h.classPayload? k).map clsShape

theorem modAncestors_go_congr {h h' : Heap} (hs : ShapeAgree h h') :
    ∀ (fuel : Nat) (mo : ObjId),
      modAncestors.go h' mo fuel = modAncestors.go h mo fuel := by
  intro fuel
  induction fuel with
  | zero => intro mo; rfl
  | succ n ih =>
    intro mo
    unfold modAncestors.go
    have := hs mo
    cases h1 : h'.classPayload? mo with
    | none =>
      cases h2 : h.classPayload? mo with
      | none => simp
      | some c => rw [h1, h2] at this; exact absurd this (by simp)
    | some c' =>
      cases h2 : h.classPayload? mo with
      | none => rw [h1, h2] at this; exact absurd this (by simp)
      | some c =>
        rw [h1, h2] at this
        simp only [Option.map_some, Option.some.injEq, clsShape, Prod.mk.injEq] at this
        obtain ⟨_, hinc, _⟩ := this
        simp only [hinc, ih]

theorem modAncestors_congr {h h' : Heap} (hs : ShapeAgree h h')
    (hsz : h'.objs.size = h.objs.size) (mo : ObjId) :
    modAncestors h' mo = modAncestors h mo := by
  unfold modAncestors
  rw [hsz]
  exact modAncestors_go_congr hs _ mo

/-- `ancestors.go` uses `modAncestors h` **unapplied** as a `flatMap` function, so
    the pointwise congruence will not rewrite there; the funext form is what
    `simp` can use. -/
theorem modAncestors_funext {h h' : Heap} (hs : ShapeAgree h h')
    (hsz : h'.objs.size = h.objs.size) : modAncestors h' = modAncestors h :=
  funext (modAncestors_congr hs hsz)

theorem ancestors_go_congr {h h' : Heap} (hs : ShapeAgree h h')
    (hsz : h'.objs.size = h.objs.size) :
    ∀ (fuel : Nat) (k : ObjId), ancestors.go h' k fuel = ancestors.go h k fuel := by
  intro fuel
  induction fuel with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    unfold ancestors.go
    have hk := hs k
    cases h1 : h'.classPayload? k with
    | none =>
      cases h2 : h.classPayload? k with
      | none => simp
      | some c => rw [h1, h2] at hk; exact absurd hk (by simp)
    | some c' =>
      cases h2 : h.classPayload? k with
      | none => rw [h1, h2] at hk; exact absurd hk (by simp)
      | some c =>
        rw [h1, h2] at hk
        simp only [Option.map_some, Option.some.injEq, clsShape, Prod.mk.injEq] at hk
        obtain ⟨hpre, hinc, hsup⟩ := hk
        simp only [hpre, hinc, hsup, modAncestors_funext hs hsz, ih]

theorem ancestors_congr {h h' : Heap} (hs : ShapeAgree h h')
    (hsz : h'.objs.size = h.objs.size) (k : ObjId) :
    ancestors h' k = ancestors h k := by
  unfold ancestors
  rw [hsz, ancestors_go_congr hs hsz]

/-! ## `defineMethod` instances -/

theorem objs_size_defineMethod (h : Heap) (cls : ObjId) (name : String) (md : MethodDef) :
    (defineMethod h cls name md).objs.size = h.objs.size := by
  unfold defineMethod
  split
  · simp [Heap.setClassPayload, Heap.set, Array.set!]
  · rfl

theorem ancestors_defineMethod (h : Heap) (cls k : ObjId) (name : String)
    (md : MethodDef) :
    ancestors (defineMethod h cls name md) k = ancestors h k :=
  ancestors_congr (fun j => shape_defineMethod h cls j name md)
    (objs_size_defineMethod h cls name md) k

/-- **`defineMethod` does not turn an object into a class, or out of being one.**
    A corollary of `shape_defineMethod` that two callers now need — the third
    conjunct of `Static.typeAgree_defineMethod`, and the singleton-shadow gate of
    `Static.crubySingletonShadow_defineMethod` (F1a). Proved once here rather than
    twice there. -/
theorem classPayload?_isSome_defineMethod (h : Heap) (cls k : ObjId) (name : String)
    (md : MethodDef) :
    ((defineMethod h cls name md).classPayload? k).isSome = (h.classPayload? k).isSome := by
  have hsh := shape_defineMethod h cls k name md
  cases h1 : (defineMethod h cls name md).classPayload? k <;>
    cases h2 : h.classPayload? k <;>
    rw [h1, h2] at hsh <;> simp_all

/-! ## Step 3: `lookup` is unchanged for a *different* method name -/

theorem find?_filter_ne {α : Type} (l : List (String × α)) {x y : String}
    (hxy : ¬ (y = x)) :
    (l.filter (·.1 != x)).find? (·.1 == y) = l.find? (·.1 == y) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hax : a.1 = x
    · have h1 : (a.1 != x) = false := by simp [hax]
      have h2 : (a.1 == y) = false := by
        simp only [beq_eq_false_iff_ne]; rw [hax]; exact fun h => hxy h.symm
      simp [List.filter, List.find?, h1, h2, ih]
    · have h1 : (a.1 != x) = true := by simp [hax]
      simp [List.filter, List.find?, h1, ih]

theorem methods_find_defineMethod (h : Heap) (cls k : ObjId) (name m : String)
    (md : MethodDef) (hne : ¬ (m = name)) :
    ((defineMethod h cls name md).classPayload? k).map
        (fun c => c.methods.find? (·.1 == m))
      = (h.classPayload? k).map (fun c => c.methods.find? (·.1 == m)) := by
  unfold defineMethod
  split
  · rename_i c hc
    by_cases hk : k = cls
    · subst hk
      simp only [Heap.setClassPayload, Heap.classPayload?, Heap.get, Heap.set]
      by_cases hb : k < h.objs.size
      · have hhead : ((name, md).1 == m) = false := by
          simp only [beq_eq_false_iff_ne]; exact fun hh => hne hh.symm
        simp [Array.getD, hb, Array.set!, List.find?, hhead, find?_filter_ne _ hne]
        unfold Heap.classPayload? Heap.get at hc
        simp [Array.getD, hb] at hc
        split at hc <;> simp_all
      · rw [classPayload?_oob h k hb] at hc; exact absurd hc (by simp)
    · simp only [Heap.setClassPayload, Heap.classPayload?, Heap.get, Heap.set]
      rw [objs_getD_set!_ne _ _ _ _ hk]
  · rfl

theorem lookup_go_defineMethod (h : Heap) (cls : ObjId) (name m : String)
    (md : MethodDef) (hne : ¬ (m = name)) :
    ∀ chain, lookup.go (defineMethod h cls name md) m chain = lookup.go h m chain := by
  intro chain
  induction chain with
  | nil => rfl
  | cons k rest ih =>
    unfold lookup.go
    have hk := methods_find_defineMethod h cls k name m md hne
    cases h1 : (defineMethod h cls name md).classPayload? k with
    | none =>
      cases h2 : h.classPayload? k with
      | none => exact ih
      | some c => rw [h1, h2] at hk; exact absurd hk (by simp)
    | some c' =>
      cases h2 : h.classPayload? k with
      | none => rw [h1, h2] at hk; exact absurd hk (by simp)
      | some c =>
        rw [h1, h2] at hk
        simp only [Option.map_some, Option.some.injEq] at hk
        dsimp only
        rw [hk]
        split <;> simp [ih]

/-- `defineMethod` preserves everything `className` reads — the name *and*
    `isModule`, since L124's anonymous-class fallback renders `#<Module:…>` or
    `#<Class:…>` by it. -/
theorem clsName_defineMethod (h : Heap) (cls k : ObjId) (name : String)
    (md : MethodDef) :
    ((defineMethod h cls name md).classPayload? k).map (fun c => (c.name, c.isModule))
      = (h.classPayload? k).map (fun c => (c.name, c.isModule)) := by
  unfold defineMethod
  split
  · rename_i c hc
    by_cases hk : k = cls
    · subst hk
      simp only [Heap.setClassPayload, Heap.classPayload?, Heap.get, Heap.set]
      by_cases hb : k < h.objs.size
      · simp [Array.getD, hb, Array.set!]
        unfold Heap.classPayload? Heap.get at hc
        simp [Array.getD, hb] at hc
        split at hc <;> simp_all
      · rw [classPayload?_oob h k hb] at hc; exact absurd hc (by simp)
    · simp only [Heap.setClassPayload, Heap.classPayload?, Heap.get, Heap.set]
      rw [objs_getD_set!_ne _ _ _ _ hk]
  · rfl

theorem className_defineMethod (h : Heap) (cls k : ObjId) (name : String)
    (md : MethodDef) : className (defineMethod h cls name md) k = className h k := by
  unfold className
  have hk := clsName_defineMethod h cls k name md
  cases h1 : (defineMethod h cls name md).classPayload? k with
  | none =>
    cases h2 : h.classPayload? k with
    | none => rfl
    | some c => rw [h1, h2] at hk; exact absurd hk (by simp)
  | some c' =>
    cases h2 : h.classPayload? k with
    | none => rw [h1, h2] at hk; exact absurd hk (by simp)
    | some c =>
      rw [h1, h2] at hk
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
      dsimp only
      rw [hk.1, hk.2]

/-- `classOf` on an immediate is heap-independent (`Heap.lean:396`), so the
    `lookup` congruence below needs no side condition for integer receivers. -/
theorem classOf_int (h : Heap) (a : Int) : classOf h (.int a) = Boot.integerId := rfl

/-- `defineMethod` rewrites one object's *payload*; `klass` and `eigen` are
    separate `Object` fields and `setClassPayload` copies them (`Heap.lean:181`),
    so `classOf` — which reads only those — is untouched. -/
theorem classOf_defineMethod (h : Heap) (cls : ObjId) (name : String)
    (md : MethodDef) (v : Value) :
    classOf (defineMethod h cls name md) v = classOf h v := by
  cases v
  case ref o =>
    have hgo : ((defineMethod h cls name md).get o).eigen = (h.get o).eigen ∧
        ((defineMethod h cls name md).get o).klass = (h.get o).klass := by
      unfold defineMethod
      split
      · rename_i c hc
        by_cases hk : o = cls
        · subst hk
          simp only [Heap.setClassPayload, Heap.get, Heap.set]
          by_cases hb : o < h.objs.size
          · simp [Array.getD, hb, Array.set!]
          · rw [classPayload?_oob h o hb] at hc; exact absurd hc (by simp)
        · simp only [Heap.setClassPayload, Heap.get, Heap.set]
          rw [objs_getD_set!_ne _ _ _ _ hk]
          exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    unfold classOf
    dsimp only
    rw [hgo.1, hgo.2]
  case bool b => cases b <;> rfl
  all_goals rfl

/-- **`lookup` is unchanged by defining a *differently named* method.** The
    name-disjointness route (§3 of the header): it avoids having to reason about
    *where* in the ancestor chain resolution lands. -/
theorem lookup_defineMethod (h : Heap) (cls : ObjId) (name m : String)
    (md : MethodDef) (v : Value) (hne : ¬ (m = name))
    (hco : classOf (defineMethod h cls name md) v = classOf h v) :
    lookup (defineMethod h cls name md) v m = lookup h v m := by
  unfold lookup
  rw [hco, ancestors_defineMethod, lookup_go_defineMethod h cls name m md hne]

end Proof
end RubyCore
