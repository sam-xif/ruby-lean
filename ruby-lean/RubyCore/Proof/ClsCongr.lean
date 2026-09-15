import RubyCore.Proof.HeapGrow

/-!
# The old heap's reads across a **class-allocating** growth (J43 / W2c)

`PlainGrow`'s global `classPayload?` agreement is exactly what a class allocation
breaks (`HeapGrow.lean`'s header), so nothing there transports the invariant
across `enterClassBody`'s fresh path. What *is* true — and what `ChainsIn` was
carried for — is that **every read the invariant makes at an old id stays inside
the old ids**: chain edges are in-bounds (`ChainsIn`), old `get`s are pinned, so
the walks compute identically. This file is that congruence suite, relativized
to `o < h.objs.size` throughout.

`ClsGrow` deliberately says nothing about the fresh ids' *contents* — the
`module'`/`defs` cases read those off the concrete step expression (the fresh
module's chain is a literal), not off the relation.
-/

namespace RubyCore
namespace Proof

open Interp

/-- A growth that may allocate **class** objects: old ids read back identically,
    nothing else promised. `payloadOld` is derived, not a field. -/
structure ClsGrow (h h' : Heap) : Prop where
  size : h.objs.size ≤ h'.objs.size
  get : ∀ o, o < h.objs.size → h'.get o = h.get o

theorem flatMap_congr_mem {α β : Type _} {l : List α} {f g : α → List β}
    (hfg : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [hfg x (by simp), ih (fun a ha => hfg a (List.mem_cons_of_mem _ ha))]

namespace ClsGrow

variable {h h' : Heap}

theorem payloadOld (hg : ClsGrow h h') {k : ObjId} (hk : k < h.objs.size) :
    h'.classPayload? k = h.classPayload? k := by
  unfold Heap.classPayload?
  rw [hg.get k hk]

/-- A push of any object is an instance. -/
theorem of_push (h : Heap) (obj : Object) : ClsGrow h ⟨h.objs.push obj⟩ :=
  ⟨by simp,
   fun o ho => by
     simp only [Heap.get, Array.getD_eq_getD_getElem?, Array.getElem?_push,
       if_neg (Nat.ne_of_lt ho)]⟩

/-- And so is a field write at a **fresh** id (the eigen-set on a just-allocated
    module). -/
theorem of_set_fresh (h : Heap) (k : ObjId) (obj : Object) (hk : h.objs.size ≤ k) :
    ClsGrow h (h.set k obj) := by
  refine ⟨by simp [Heap.set, Array.set!], fun o ho => ?_⟩
  simp only [Heap.set, Heap.get]
  rw [objs_getD_set!_ne _ _ _ _ (by omega)]

theorem trans {h'' : Heap} (hg : ClsGrow h h') (hg' : ClsGrow h' h'') :
    ClsGrow h h'' :=
  ⟨Nat.le_trans hg.size hg'.size,
   fun o ho => by rw [hg'.get o (Nat.lt_of_lt_of_le ho hg.size), hg.get o ho]⟩

theorem className_old (hg : ClsGrow h h') {k : ObjId} (hk : k < h.objs.size) :
    className h' k = className h k := by
  unfold className
  rw [hg.payloadOld hk]

theorem classPayload?_isSome_old (hg : ClsGrow h h') {k : ObjId}
    (hk : k < h.objs.size) :
    (h'.classPayload? k).isSome = (h.classPayload? k).isSome := by
  rw [hg.payloadOld hk]

/-- `classOf` at an old value: the fields are pinned, and the *answer* is old
    (`ChainsIn`'s two field clauses). -/
theorem classOf_old (hg : ClsGrow h h') (hch : ChainsIn h) {o : ObjId}
    (ho : o < h.objs.size) :
    classOf h' (.ref o) = classOf h (.ref o) := by
  simp only [classOf, hg.get o ho]

theorem classOf_lt (hch : ChainsIn h) {o : ObjId} (ho : o < h.objs.size) :
    classOf h (.ref o) < h.objs.size := by
  simp only [classOf]
  cases he : (h.get o).eigen with
  | some e => exact hch.eigen o ho e he
  | none => exact hch.klass o ho

/-- `modAncestors.go` at any fuel is pinned at old start ids. -/
theorem modAncestors_go_old (hg : ClsGrow h h') (hch : ChainsIn h) :
    ∀ (fuel : Nat) (mo : ObjId), mo < h.objs.size →
      modAncestors.go h' mo fuel = modAncestors.go h mo fuel := by
  intro fuel
  induction fuel with
  | zero => intro mo _; rfl
  | succ fuel ih =>
    intro mo hmo
    unfold modAncestors.go
    rw [hg.payloadOld hmo]
    cases hcp : h.classPayload? mo with
    | none => rfl
    | some c =>
      dsimp only
      have hincl := (hch.chain mo c hmo hcp).2.1
      congr 1
      refine flatMap_congr_mem ?_
      intro i hi
      exact ih i (hincl i (List.mem_reverse.mp hi))

/-- `ancestors.go` likewise — the superclass recursion and both mixin splices stay
    among old ids. The spliced `modAncestors` are the *full-fuel* ones, so this
    needs `Saturated` on the old heap to line the two fuels up. -/
theorem ancestors_go_old (hg : ClsGrow h h') (hch : ChainsIn h)
    (hsat : Saturated h) :
    ∀ (fuel : Nat) (k : ObjId), k < h.objs.size →
      ancestors.go h' k fuel = ancestors.go h k fuel := by
  intro fuel
  induction fuel with
  | zero => intro k _; rfl
  | succ fuel ih =>
    intro k hk
    unfold ancestors.go
    rw [hg.payloadOld hk]
    cases hcp : h.classPayload? k with
    | none => rfl
    | some c =>
      dsimp only
      obtain ⟨hsup, hincl, hpre⟩ := hch.chain k c hk hcp
      have hmodEq : ∀ i, i < h.objs.size → modAncestors h' i = modAncestors h i := by
        intro i hi
        unfold modAncestors
        rw [modAncestors_go_old hg hch _ i hi]
        rw [modAncestors_go_ge hsat.1 (Nat.succ_le_succ hg.size) i]
      congr 1
      · congr 1
        · exact flatMap_congr_mem
            (fun p hp => hmodEq p (hpre p (List.mem_reverse.mp hp)))
        · congr 1
          exact flatMap_congr_mem
            (fun i hi => hmodEq i (hincl i (List.mem_reverse.mp hi)))
      · cases hs : c.superclass with
        | none => rfl
        | some s => exact ih s (hsup s hs)

/-- The headline: an old id's ancestor chain is unmoved. -/
theorem ancestors_old (hg : ClsGrow h h') (hch : ChainsIn h) (hsat : Saturated h)
    {k : ObjId} (hk : k < h.objs.size) :
    ancestors h' k = ancestors h k := by
  unfold ancestors
  rw [ancestors_go_old hg hch hsat _ k hk,
    ancestors_go_ge hsat.2 (Nat.succ_le_succ hg.size) k]

/-- The walk visits only old ids (the closure `ChainsIn` promises). -/
theorem modAncestors_go_mem_lt (hch : ChainsIn h) :
    ∀ (fuel : Nat) (mo : ObjId), mo < h.objs.size →
      ∀ j ∈ modAncestors.go h mo fuel, j < h.objs.size := by
  intro fuel
  induction fuel with
  | zero => intro mo hmo j hj; simp only [modAncestors.go] at hj
            rw [List.mem_singleton.mp hj]; exact hmo
  | succ fuel ih =>
    intro mo hmo j hj
    unfold modAncestors.go at hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hmo
    · cases hcp : h.classPayload? mo with
      | none => rw [hcp] at hj; simp at hj
      | some c =>
        rw [hcp] at hj
        obtain ⟨i, hi, hji⟩ := List.mem_flatMap.mp hj
        exact ih i ((hch.chain mo c hmo hcp).2.1 i (List.mem_reverse.mp hi)) j hji

theorem ancestors_go_mem_lt (hch : ChainsIn h) :
    ∀ (fuel : Nat) (k : ObjId), k < h.objs.size →
      ∀ j ∈ ancestors.go h k fuel, j < h.objs.size := by
  intro fuel
  induction fuel with
  | zero => intro k _ j hj; simp [ancestors.go] at hj
  | succ fuel ih =>
    intro k hk j hj
    unfold ancestors.go at hj
    cases hcp : h.classPayload? k with
    | none =>
      rw [hcp] at hj
      rw [List.mem_singleton.mp hj]; exact hk
    | some c =>
      rw [hcp] at hj
      obtain ⟨hsup, hincl, hpre⟩ := hch.chain k c hk hcp
      have hmodmem : ∀ i, i < h.objs.size → ∀ j' ∈ modAncestors h i,
          j' < h.objs.size := by
        intro i hi j' hj'
        exact modAncestors_go_mem_lt hch _ i hi j' hj'
      rcases List.mem_append.mp hj with hj2 | hj3
      · rcases List.mem_append.mp hj2 with hj4 | hj5
        · obtain ⟨p, hp, hjp⟩ := List.mem_flatMap.mp hj4
          exact hmodmem p (hpre p (List.mem_reverse.mp hp)) j hjp
        · rcases List.mem_cons.mp hj5 with rfl | hj6
          · exact hk
          · obtain ⟨i, hi, hji⟩ := List.mem_flatMap.mp hj6
            exact hmodmem i (hincl i (List.mem_reverse.mp hi)) j hji
      · cases hs : c.superclass with
        | none => rw [hs] at hj3; simp at hj3
        | some s => rw [hs] at hj3; exact ih s (hsup s hs) j hj3

theorem ancestors_mem_lt (hch : ChainsIn h) {k : ObjId} (hk : k < h.objs.size) :
    ∀ j ∈ ancestors h k, j < h.objs.size := by
  intro j hj
  unfold ancestors at hj
  -- the fold is a de-dup: membership in the fold implies membership in the walk
  have hsub : ∀ (l : List ObjId) (acc : List ObjId),
      j ∈ l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc →
      j ∈ acc ∨ j ∈ l := by
    intro l
    induction l with
    | nil => intro acc hjm; exact Or.inl hjm
    | cons x xs ih =>
      intro acc hjm
      simp only [List.foldl] at hjm
      by_cases hc : acc.contains x
      · simp only [hc, if_true] at hjm
        rcases ih acc hjm with hja | hjl
        · exact Or.inl hja
        · exact Or.inr (List.mem_cons_of_mem _ hjl)
      · simp only [hc, if_false] at hjm
        rcases ih (acc ++ [x]) hjm with hja | hjl
        · rcases List.mem_append.mp hja with hja | hjx
          · exact Or.inl hja
          · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hjx)))
        · exact Or.inr (List.mem_cons_of_mem _ hjl)
  rcases hsub _ [] hj with hja | hjl
  · simp at hja
  · exact ancestors_go_mem_lt hch _ k hk j hjl

end ClsGrow

end Proof
end RubyCore
