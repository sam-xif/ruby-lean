import Denote.Grow

/-!
# `Denote/Local.lean` — rebinding a local, and what a type's meaning survives of it

`Denote/Ext.lean`/`Denote/Grow.lean` did allocation. This file does the other machine change
a leaf-ish rule makes: **`Machine.setLocal`**, the write behind `Judge.vasgn`/`vasgnAlias`.

The two are not the same problem, and the difference is the whole reason
`found-issues.md` §F1 existed. An allocation cannot change what a value *is*, so `denM`
transports across it unconditionally (`denM_ext`). A rebinding can: `denM`'s `clos` arm reads
the captured frame's locals through `closLocal`, so `f = lambda { x }` stops denoting
`clos {x: Integer}` the moment `x` holds a String. The transport therefore carries a **side
condition**, and that side condition is `capStale` — the same function `Judge.vasgn` uses to
decide which bindings to widen. The checker's fix and the semantic transport are the same
predicate, which is what it means for the fix to be the right one.

## What `setLocal` actually does

```
def setLocal (m) (x) (v) :=
  let start  := m.stack.headD 0
  let target := owner start (m.frames.size + 1)   -- first frame on the captured chain
  { m with frames := m.frames.set! target          --  that binds `x`, else `start`
      { m.frames.getD target default with
        locals := (x, v) :: (m.frames.getD target default).locals.filter (·.1 != x) } }
```

One `Array.set!`, at an index the lemmas below never need to name: everything here is proved
against `∃ T, frames' = frames.set! T (write T)`, which is `rfl`. Three consequences and one
subtlety:

* **Every field but `locals` is untouched**, at every frame — so `self`, `blk`, `kind`,
  `meth` and `captured` are rewrites, and the heap, the stack and the frame *count* are `rfl`.
* **A lookup of any name but `x` is unchanged**, at every frame, which is `find?_filter_ne`
  (`RubyCore/Proof/HeapFacts.lean`) one layer up. So `frameLocal`/`getLocal` agree on `y ≠ x`
  by an induction that never mentions the target.
* **A lookup of `x` is either the new value or the old one** — the target is on *some* chain,
  not necessarily the one being read, so the disjunction is the honest statement. It is also
  all the `clos` arm needs: `capStale` says the recorded type is the new value's type, and the
  old value already had it.
* **The subtlety is `getLocal x` itself**, where the disjunction is not enough — the rule
  binds `x` and the obligation asks for the value that binding names. `getLocal_setLocal` is
  the exact answer, and it is a **lockstep** induction: `setLocal.owner` and `getLocal.go`
  walk the same chain by the same steps (`any (·.1 == x)` versus `find? (·.1 == x)`), so the
  frame the write lands on is the frame the read stops at. The one machine where that fails is
  one with no current frame at all (`stack.headD 0` out of range), where `set!` is a no-op and
  the read answers `nil`; `StateOk.frameInRange` rules it out.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The write, with its target left abstract -/

/-- The frame `setLocal` writes at index `T`. -/
def setFrame (m : Machine) (x : String) (v : Value) (T : FrameId) : Frame :=
  { m.frames.getD T default with
    locals := (x, v) :: (m.frames.getD T default).locals.filter (·.1 != x) }

/-- `m` with the `setLocal` write performed at a *given* target — the shape every lemma below
is proved against, so none of them has to know which frame `setLocal` picked. -/
def setAt (m : Machine) (x : String) (v : Value) (T : FrameId) : Machine :=
  { m with frames := m.frames.set! T (setFrame m x v T) }

/-- `setLocal` is `setAt` at the target its own `owner` walk found. `rfl`. -/
theorem setLocal_eq_setAt (m : Machine) (x : String) (v : Value) :
    m.setLocal x v = setAt m x v (Machine.setLocal.owner m x (m.stack.headD 0)
      (m.stack.headD 0) (m.frames.size + 1)) := rfl

@[simp] theorem setAt_heap (m : Machine) (x : String) (v : Value) (T : FrameId) :
    (setAt m x v T).heap = m.heap := rfl

@[simp] theorem setAt_stack (m : Machine) (x : String) (v : Value) (T : FrameId) :
    (setAt m x v T).stack = m.stack := rfl

@[simp] theorem setAt_framesSize (m : Machine) (x : String) (v : Value) (T : FrameId) :
    (setAt m x v T).frames.size = m.frames.size := by
  simp [setAt, Array.set!]

/-! ## Array facts, `Frame` flavour

Restated here rather than imported: `RubyCore/Proof/Static/Locals.lean`'s copies live under
the `Judgment`/`Static` tree, which this package does not otherwise depend on. -/

theorem framesD_set!_ne (a : Array Frame) (i j : Nat) (f : Frame) (h : j ≠ i) :
    (a.set! i f).getD j default = a.getD j default := by
  have hsz : (a.set! i f).size = a.size := by simp [Array.set!]
  by_cases hj : j < a.size
  · simp only [Array.getD]
    rw [dif_pos (hsz ▸ hj), dif_pos hj]
    exact Array.getElem_setIfInBounds_ne hj (Ne.symm h)
  · simp only [Array.getD]
    rw [dif_neg (hsz ▸ hj), dif_neg hj]

theorem framesD_set!_self (a : Array Frame) (i : Nat) (f : Frame) (h : i < a.size) :
    (a.set! i f).getD i default = f := by
  simp [Array.getD, h]

theorem framesD_set!_oob (a : Array Frame) (i : Nat) (f : Frame) (h : ¬ i < a.size) :
    (a.set! i f).getD i default = a.getD i default := by
  have hsz : (a.set! i f).size = a.size := by simp [Array.set!]
  simp only [Array.getD]
  rw [dif_neg (hsz ▸ h), dif_neg h]

/-! ## What one frame reads back as -/

/-- The captured chain is unmoved: `setFrame` copies every field but `locals`. -/
theorem setAt_captured (m : Machine) (x : String) (v : Value) (T : FrameId) (i : FrameId) :
    ((setAt m x v T).frames.getD i default).captured
      = (m.frames.getD i default).captured := by
  by_cases hi : i = T
  · subst hi
    by_cases hb : i < m.frames.size
    · simp only [setAt, framesD_set!_self _ _ _ hb, setFrame]
    · simp only [setAt, framesD_set!_oob _ _ _ hb]
  · simp only [setAt, framesD_set!_ne _ _ _ _ hi]

theorem setAt_self (m : Machine) (x : String) (v : Value) (T : FrameId) (i : FrameId) :
    ((setAt m x v T).frames.getD i default).self = (m.frames.getD i default).self := by
  by_cases hi : i = T
  · subst hi
    by_cases hb : i < m.frames.size
    · simp only [setAt, framesD_set!_self _ _ _ hb, setFrame]
    · simp only [setAt, framesD_set!_oob _ _ _ hb]
  · simp only [setAt, framesD_set!_ne _ _ _ _ hi]

/-- A lookup of any name but `x` reads back unchanged, at every frame. -/
theorem setAt_blk (m : Machine) (x : String) (v : Value) (T : FrameId) (i : FrameId) :
    ((setAt m x v T).frames.getD i default).blk = (m.frames.getD i default).blk := by
  by_cases hi : i = T
  · subst hi
    by_cases hb : i < m.frames.size
    · simp only [setAt, framesD_set!_self _ _ _ hb, setFrame]
    · simp only [setAt, framesD_set!_oob _ _ _ hb]
  · simp only [setAt, framesD_set!_ne _ _ _ _ hi]

theorem setAt_kind (m : Machine) (x : String) (v : Value) (T : FrameId) (i : FrameId) :
    ((setAt m x v T).frames.getD i default).kind = (m.frames.getD i default).kind := by
  by_cases hi : i = T
  · subst hi
    by_cases hb : i < m.frames.size
    · simp only [setAt, framesD_set!_self _ _ _ hb, setFrame]
    · simp only [setAt, framesD_set!_oob _ _ _ hb]
  · simp only [setAt, framesD_set!_ne _ _ _ _ hi]

theorem setAt_defVis (m : Machine) (x : String) (v : Value) (T : FrameId) (i : FrameId) :
    ((setAt m x v T).frames.getD i default).defVis = (m.frames.getD i default).defVis := by
  by_cases hi : i = T
  · subst hi
    by_cases hb : i < m.frames.size
    · simp only [setAt, framesD_set!_self _ _ _ hb, setFrame]
    · simp only [setAt, framesD_set!_oob _ _ _ hb]
  · simp only [setAt, framesD_set!_ne _ _ _ _ hi]

theorem setAt_meth (m : Machine) (x : String) (v : Value) (T : FrameId) (i : FrameId) :
    ((setAt m x v T).frames.getD i default).meth = (m.frames.getD i default).meth := by
  by_cases hi : i = T
  · subst hi
    by_cases hb : i < m.frames.size
    · simp only [setAt, framesD_set!_self _ _ _ hb, setFrame]
    · simp only [setAt, framesD_set!_oob _ _ _ hb]
  · simp only [setAt, framesD_set!_ne _ _ _ _ hi]

/-- The lexical constant scope and the definee are frame fields too, and `setFrame` copies
them like the rest — which is what `ConstScopeOk` (`Denote/Sem/State.lean`) is stated over. -/
theorem setAt_cref (m : Machine) (x : String) (v : Value) (T : FrameId) (i : FrameId) :
    ((setAt m x v T).frames.getD i default).cref = (m.frames.getD i default).cref := by
  by_cases hi : i = T
  · subst hi
    by_cases hb : i < m.frames.size
    · simp only [setAt, framesD_set!_self _ _ _ hb, setFrame]
    · simp only [setAt, framesD_set!_oob _ _ _ hb]
  · simp only [setAt, framesD_set!_ne _ _ _ _ hi]

theorem setAt_defmod (m : Machine) (x : String) (v : Value) (T : FrameId) (i : FrameId) :
    ((setAt m x v T).frames.getD i default).defmod = (m.frames.getD i default).defmod := by
  by_cases hi : i = T
  · subst hi
    by_cases hb : i < m.frames.size
    · simp only [setAt, framesD_set!_self _ _ _ hb, setFrame]
    · simp only [setAt, framesD_set!_oob _ _ _ hb]
  · simp only [setAt, framesD_set!_ne _ _ _ _ hi]

theorem setAt_find_ne (m : Machine) (x : String) (v : Value) (T : FrameId) (i : FrameId)
    {y : String} (hy : ¬ (y = x)) :
    ((setAt m x v T).frames.getD i default).locals.find? (·.1 == y)
      = ((m.frames.getD i default).locals.find? (·.1 == y)) := by
  by_cases hi : i = T
  · subst hi
    by_cases hb : i < m.frames.size
    · simp only [setAt, framesD_set!_self _ _ _ hb, setFrame, List.find?]
      have : ((x, v).1 == y) = false := by simpa using fun h => hy h.symm
      rw [this]
      exact Proof.find?_filter_ne _ hy
    · simp only [setAt, framesD_set!_oob _ _ _ hb]
  · simp only [setAt, framesD_set!_ne _ _ _ _ hi]

/-- At the target, `x` reads back as the new value. -/
theorem setAt_find_self (m : Machine) (x : String) (v : Value) (T : FrameId)
    (hb : T < m.frames.size) :
    ((setAt m x v T).frames.getD T default).locals.find? (·.1 == x) = some (x, v) := by
  simp only [setAt, framesD_set!_self _ _ _ hb, setFrame, List.find?]
  simp

/-! ## The chain walks

`frameLocal.go` and `Machine.getLocal.go` are the same walk from different starting frames,
so each gets the same three lemmas: agreement off `x`, a disjunction at `x`, and — for
`getLocal` only, where it is needed — the exact answer. -/

theorem frameLocal_go_setAt_ne (m : Machine) (x : String) (v : Value) (T : FrameId)
    {y : String} (hy : ¬ (y = x)) :
    ∀ (fuel : Nat) (fid : FrameId),
      frameLocal.go (setAt m x v T) y fid fuel = frameLocal.go m y fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [frameLocal.go, setAt_find_ne m x v T fid hy, setAt_captured]
    split
    · rfl
    · split
      · exact ih _
      · rfl

theorem getLocal_go_setAt_ne (m : Machine) (x : String) (v : Value) (T : FrameId)
    {y : String} (hy : ¬ (y = x)) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.getLocal.go (setAt m x v T) y fid fuel = Machine.getLocal.go m y fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [Machine.getLocal.go, setAt_find_ne m x v T fid hy, setAt_captured]
    split
    · rfl
    · split
      · exact ih _
      · rfl

/-- **The write, seen from one frame**: either this frame is the target and now answers the
new value for `x`, or it reads back exactly as it did. The three inductions below all case on
this and nothing else. -/
theorem setAt_frame_or (m : Machine) (x : String) (v : Value) (T fid : FrameId) :
    ((setAt m x v T).frames.getD fid default).locals.find? (·.1 == x) = some (x, v)
    ∨ (setAt m x v T).frames.getD fid default = m.frames.getD fid default := by
  by_cases h1 : fid = T
  · subst h1
    by_cases hb : fid < m.frames.size
    · exact Or.inl (setAt_find_self m x v fid hb)
    · exact Or.inr (by simpa [setAt] using framesD_set!_oob m.frames fid (setFrame m x v fid) hb)
  · exact Or.inr (framesD_set!_ne _ _ _ _ h1)

/-- **At `x`, the walk answers the new value or the old one.** The target is on the *current*
frame's chain, which need not be the chain being read, so this is the honest statement — and
it is what the `clos` arm needs, since `capStale` makes both answers have the recorded type. -/
theorem frameLocal_go_setAt_self (m : Machine) (x : String) (v : Value) (T : FrameId) :
    ∀ (fuel : Nat) (fid : FrameId),
      frameLocal.go (setAt m x v T) x fid fuel = v ∨
      frameLocal.go (setAt m x v T) x fid fuel = frameLocal.go m x fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; exact Or.inr rfl
  | succ n ih =>
    intro fid
    rcases setAt_frame_or m x v T fid with h1 | h1
    · exact Or.inl (by simp only [frameLocal.go, h1])
    · simp only [frameLocal.go, h1]
      cases hfind : ((m.frames.getD fid default).locals.find? (·.1 == x)) with
      | some p => exact Or.inr rfl
      | none =>
        cases hcap : (m.frames.getD fid default).captured with
        | some q => exact ih q
        | none => exact Or.inr rfl

theorem getLocal_go_setAt_self (m : Machine) (x : String) (v : Value) (T : FrameId) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.getLocal.go (setAt m x v T) x fid fuel = v ∨
      Machine.getLocal.go (setAt m x v T) x fid fuel = Machine.getLocal.go m x fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; exact Or.inr rfl
  | succ n ih =>
    intro fid
    rcases setAt_frame_or m x v T fid with h1 | h1
    · exact Or.inl (by simp only [Machine.getLocal.go, h1])
    · simp only [Machine.getLocal.go, h1]
      cases hfind : ((m.frames.getD fid default).locals.find? (·.1 == x)) with
      | some p => exact Or.inr rfl
      | none =>
        cases hcap : (m.frames.getD fid default).captured with
        | some q => exact ih q
        | none => exact Or.inr rfl

/-! ## The lockstep

`setLocal.owner` and `getLocal.go` walk the same chain, stopping at the same frame — one
testing `any (·.1 == x)`, the other `find? (·.1 == x)`. So the frame the write lands on is the
frame the read stops at, and `getLocal x` after the write is exactly the value written. The
second disjunct is the walk running out of chain or fuel, where `owner` falls back to the
starting frame — and *that* frame is where the write went, so the read finds it immediately. -/

theorem find?_eq_none_of_any_false {α : Type} (l : List α) (p : α → Bool)
    (h : l.any p = false) : l.find? p = none := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp [List.find?, h.1, ih h.2]

theorem lt_of_any_locals {m : Machine} {fid : FrameId} {x : String}
    (h : (m.frames.getD fid default).locals.any (·.1 == x) = true) : fid < m.frames.size := by
  rcases Nat.lt_or_ge fid m.frames.size with hc | hc
  · exact hc
  · rw [Array.getD, dif_neg (by omega)] at h
    exact absurd h (by simp [show (default : Frame).locals = [] from rfl])

theorem getLocal_go_owner (m : Machine) (x : String) (v : Value) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.getLocal.go
        (setAt m x v (Machine.setLocal.owner m x (m.stack.headD 0) fid fuel)) x fid fuel = v
      ∨ Machine.setLocal.owner m x (m.stack.headD 0) fid fuel = m.stack.headD 0 := by
  intro fuel
  induction fuel with
  | zero => intro fid; exact Or.inr rfl
  | succ n ih =>
    intro fid
    by_cases hany : (m.frames.getD fid default).locals.any (·.1 == x) = true
    · -- The walk stops here, and so does the write.
      have hb : fid < m.frames.size := lt_of_any_locals hany
      have hown : Machine.setLocal.owner m x (m.stack.headD 0) fid (n + 1) = fid := by
        simp only [Machine.setLocal.owner, hany, if_true]
      refine Or.inl ?_
      rw [hown]
      simp only [Machine.getLocal.go, setAt_find_self m x v fid hb]
    · have hany' : (m.frames.getD fid default).locals.any (·.1 == x) = false := by
        rw [Bool.not_eq_true] at hany; exact hany
      have hnone : (m.frames.getD fid default).locals.find? (·.1 == x) = none :=
        find?_eq_none_of_any_false _ _ hany'
      cases hcap : (m.frames.getD fid default).captured with
      | none =>
        refine Or.inr ?_
        simp only [Machine.setLocal.owner, hany', hcap]
        simp
      | some q =>
        have hown : Machine.setLocal.owner m x (m.stack.headD 0) fid (n + 1)
            = Machine.setLocal.owner m x (m.stack.headD 0) q n := by
          simp only [Machine.setLocal.owner, hany', hcap]; simp
        rw [hown]
        rcases setAt_frame_or m x v (Machine.setLocal.owner m x (m.stack.headD 0) q n) fid
          with h1 | h1
        · exact Or.inl (by simp only [Machine.getLocal.go, h1])
        · rcases ih q with hq | hq
          · exact Or.inl (by simp only [Machine.getLocal.go, h1, hnone, hcap]; exact hq)
          · exact Or.inr hq

/-! ## `getLocal` after `setLocal` -/

theorem getLocal_setLocal_ne (m : Machine) (x : String) (v : Value) {y : String}
    (hy : ¬ (y = x)) : (m.setLocal x v).getLocal y = m.getLocal y := by
  rw [setLocal_eq_setAt]
  simp only [Machine.getLocal, setAt_stack, setAt_framesSize]
  exact getLocal_go_setAt_ne m x v _ hy _ _

/-- **The exact answer**, and the one place the disjunction is not enough: the rule binds `x`
and the obligation asks about the value that binding names. The hypothesis is what rules out
the degenerate machine with no current frame, where `set!` is a no-op. -/
theorem getLocal_setLocal_self (m : Machine) (x : String) (v : Value)
    (hb : m.stack.headD 0 < m.frames.size) : (m.setLocal x v).getLocal x = v := by
  rw [setLocal_eq_setAt]
  simp only [Machine.getLocal, setAt_stack, setAt_framesSize]
  rcases getLocal_go_owner m x v (m.frames.size + 1) (m.stack.headD 0) with h | h
  · exact h
  · rw [h]
    simp only [Machine.getLocal.go, setAt_find_self m x v _ hb]

/-! ## `Later`, and the transport

A rebinding is a `Later` (heap untouched, stack and frame count untouched), which is what
carries the arrow arm and `AsmsOk` across it for free. Everything else is either heap-only or
goes through the `clos` arm, where `capStale` is the side condition. -/

theorem setLocal_later (m : Machine) (x : String) (v : Value) : Later m (m.setLocal x v) where
  stack := rfl
  frameCount := by rw [setLocal_eq_setAt]; exact setAt_framesSize m x v _
  size := Nat.le_refl _
  klass := fun _ _ => rfl
  eigen := fun _ _ => rfl
  payloadObj := fun _ _ => rfl
  frozen := fun _ _ => rfl
  payload := fun _ => rfl
  ancestors := fun _ => rfl

/-- **What a closure's captured environment reads as after the write**: unchanged, or the new
value and only at `x`. Exactly the shape `denM`'s `clos` arm needs, and the reason the
transport below has a side condition rather than being unconditional. -/
theorem closLocal_setLocal (m : Machine) (x : String) (w : Value) (cl : Closure) (y : String) :
    closLocal (m.setLocal x w) cl y = closLocal m cl y ∨
      (y = x ∧ closLocal (m.setLocal x w) cl y = w) := by
  -- L266: a capture-free closure reads `nil` at every name, before the write and after it.
  cases hc : cl.captured with
  | none => exact Or.inl (by simp only [closLocal, hc, frameLocal?])
  | some p =>
  by_cases hy : y = x
  · subst hy
    rw [setLocal_eq_setAt]
    simp only [closLocal, hc, frameLocal?, frameLocal, setAt_framesSize]
    rcases frameLocal_go_setAt_self m y w
      (Machine.setLocal.owner m y (m.stack.headD 0) (m.stack.headD 0) (m.frames.size + 1))
      (m.frames.size + 1) p with h | h
    · exact Or.inr ⟨by simp, h⟩
    · exact Or.inl h
  · refine Or.inl ?_
    rw [setLocal_eq_setAt]
    simp only [closLocal, hc, frameLocal?, frameLocal, setAt_framesSize]
    exact frameLocal_go_setAt_ne m x w _ hy _ _

theorem closSelf_setLocal (m : Machine) (x : String) (w : Value) (cl : Closure) :
    closSelf (m.setLocal x w) cl = closSelf m cl := by
  rw [setLocal_eq_setAt]; exact setAt_self m x w _ (cl.captured.getD 0)

/-- **A type's meaning survives a rebinding, unless it recorded one.**

`capStale x τ' σ = false` is the side condition, and it is the *same* predicate
`Judge.vasgn` uses to decide which bindings to widen (`Ratchet/Ty.lean` §Stale closure
captures). The checker's fix and the semantic transport being one function is what makes the
fix the right one rather than a patch that happens to reject the counterexample.

The spine half carries the shape the `clos` arm produces: `closLocal` after the write agrees
with `closLocal` before it *except possibly at `x`*, where it is the new value — which is
exactly `frameLocal_go_setAt_self`/`_ne`. At such an entry the spine's recorded type is `τ'`
(that is the `capStale` clause), so the new value has it by `hw`. -/
theorem denM_setLocal_aux {m : Machine} {x : String} {w : Value} {τ' : Ty}
    (hw : denM τ' m w) : ∀ τ : Ty,
    (capStale x τ' τ = false → ∀ v, denM τ m v → denM τ (m.setLocal x w) v) ∧
    (capStale x τ' τ = false → ∀ (seen : List String) g g',
      (∀ y, g' y = g y ∨ (y = x ∧ g' y = w)) →
      denSpineFrom seen τ m g → denSpineFrom seen τ (m.setLocal x w) g') := by
  intro τ
  induction τ with
  | int | bool | nilT | sym | float | any | never =>
    exact ⟨fun _ _ h => by rwa [denM] at h ⊢, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | ivar0 =>
    exact ⟨fun _ _ h => absurd h (by simp [denM]), fun _ _ _ _ _ _ => by simp [denSpineFrom]⟩
  | cls n =>
    exact ⟨fun _ _ h => by rw [denM] at h ⊢; rwa [show (m.setLocal x w).heap = m.heap from rfl],
           fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | clsOf n =>
    exact ⟨fun _ _ h => by rw [denM] at h ⊢; rwa [show (m.setLocal x w).heap = m.heap from rfl],
           fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
  | nilable τ ih =>
    refine ⟨fun hs _ h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    rw [capStale] at hs
    exact h.imp id (ih.1 hs _)
  | union σ τ ihσ ihτ =>
    refine ⟨fun hs _ h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    rw [capStale, Bool.or_eq_false_iff] at hs
    exact h.imp (ihσ.1 hs.1 _) (ihτ.1 hs.2 _)
  | sameAs y τ ih =>
    refine ⟨fun hs _ h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    rw [capStale] at hs
    exact ih.1 hs _ h
  | arrayOf e ih =>
    refine ⟨fun hs v h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    rw [capStale] at hs
    obtain ⟨xs, hx, hall⟩ := h
    exact ⟨xs, hx, fun y hy => ih.1 hs y (hall y hy)⟩
  | hashOf a b iha ihb =>
    refine ⟨fun hs v h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    rw [capStale, Bool.or_eq_false_iff] at hs
    obtain ⟨es, hx, hall⟩ := h
    exact ⟨es, hx, fun p hp => ⟨iha.1 hs.1 _ (hall p hp).1, ihb.1 hs.2 _ (hall p hp).2⟩⟩
  | arrow0 r ihr =>
    refine ⟨fun _ f h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    exact ⟨h.1, fun m₃ he₃ => h.2 m₃ ((setLocal_later m x w).trans he₃)⟩
  | arrowCons p rest ihp ihrest =>
    refine ⟨fun _ f h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    exact ⟨h.1, fun m₃ he₃ => h.2 m₃ ((setLocal_later m x w).trans he₃)⟩
  | inst n I ihI =>
    refine ⟨fun hs v h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    rw [capStale] at hs
    refine ⟨h.1, ihI.2 hs _ _ _ (fun _ => Or.inl rfl) h.2⟩
  | ivarCons y σ rest ihσ ihrest =>
    refine ⟨fun _ _ h => absurd h (by simp [denM]), fun hs seen g g' hg h => ?_⟩
    rw [denSpineFrom] at h ⊢
    rw [capStale, Bool.or_eq_false_iff, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hs
    obtain ⟨⟨hkey, hσ⟩, hrest⟩ := hs
    refine ⟨?_, ihrest.2 hrest _ g g' hg h.2⟩
    -- A shadowed entry stays shadowed: `seen` is threaded unchanged, so the `y ∈ seen`
    -- disjunct transports with no work at all.
    rcases h.1 with hin | h1
    · exact Or.inl hin
    refine Or.inr ?_
    rcases hg y with hgy | ⟨rfl, hgy⟩
    · rw [hgy]; exact ihσ.1 hσ _ h1
    · -- The one entry the write can have moved: the spine records `x`, so `capStale`'s key
      -- clause says it records it at `τ'`, and the new value has `τ'` by `hw`.
      have hστ : σ = τ' := by
        rcases hkey with hk | hk
        · exact absurd hk (by simp)
        · simp only [Bool.not_eq_false', decide_eq_true_eq] at hk; exact hk
      rw [hgy]
      exact ihσ.1 hσ w (by rw [hστ]; exact hw)
  | clos idx cap selfT ihcap ihself =>
    refine ⟨fun hs f h => ?_, fun _ _ _ _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    rw [capStale, Bool.or_eq_false_iff] at hs
    obtain ⟨cl, hpc, hspine, hself⟩ := h
    refine ⟨cl, hpc, ?_, ?_⟩
    · exact ihcap.2 hs.1 _ _ _ (fun y => closLocal_setLocal m x w cl y) hspine
    · rcases hself with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by rw [closSelf_setLocal]; exact ihself.1 hs.2 _ h1)

theorem denM_setLocal {τ τ' : Ty} {m : Machine} {x : String} {w v : Value}
    (hw : denM τ' m w) (hs : capStale x τ' τ = false) (h : denM τ m v) :
    denM τ (m.setLocal x w) v := (denM_setLocal_aux hw τ).1 hs v h

theorem denSpine_setLocal {τ τ' : Ty} {m : Machine} {x : String} {w : Value}
    {g : String → Value} (hw : denM τ' m w) (hs : capStale x τ' τ = false)
    (h : denSpine τ m g) : denSpine τ (m.setLocal x w) g :=
  (denM_setLocal_aux hw τ).2 hs [] g g (fun _ => Or.inl rfl) h

/-! ## What the write does to the rest of the machine -/

@[simp] theorem setLocal_heap (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).heap = m.heap := rfl

@[simp] theorem setLocal_stack (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).stack = m.stack := rfl

/-- The write touches `frames` and nothing else, so the control word and the continuation read
back unchanged. Needed by the `asgnK` frame's clauses, which have to say what machine the
frame leaves behind. -/
@[simp] theorem setLocal_kont (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).kont = m.kont := rfl

@[simp] theorem setLocal_ctl (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).ctl = m.ctl := rfl

/-- Every frame field but `locals` is copied, so the current frame's `self`, `blk`, `kind` and
`meth` all read back unchanged — which is what `SelfSpineOk`, `FrameOk`, `BlockTyOk` and
`SelfTyOk` are stated over. -/
theorem currentFrame_setLocal_self (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).currentFrame.self = m.currentFrame.self := by
  simp only [Machine.currentFrame, setLocal_stack]
  cases m.stack with
  | nil => rfl
  | cons fid rest => rw [setLocal_eq_setAt]; exact setAt_self m x w _ fid

theorem currentFrame_setLocal_blk (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).currentFrame.blk = m.currentFrame.blk := by
  simp only [Machine.currentFrame, setLocal_stack]
  cases m.stack with
  | nil => rfl
  | cons fid rest => rw [setLocal_eq_setAt]; exact setAt_blk m x w _ fid

theorem currentFrame_setLocal_kind (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).currentFrame.kind = m.currentFrame.kind := by
  simp only [Machine.currentFrame, setLocal_stack]
  cases m.stack with
  | nil => rfl
  | cons fid rest => rw [setLocal_eq_setAt]; exact setAt_kind m x w _ fid

theorem currentFrame_setLocal_meth (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).currentFrame.meth = m.currentFrame.meth := by
  simp only [Machine.currentFrame, setLocal_stack]
  cases m.stack with
  | nil => rfl
  | cons fid rest => rw [setLocal_eq_setAt]; exact setAt_meth m x w _ fid

theorem currentFrame_setLocal_cref (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).currentFrame.cref = m.currentFrame.cref := by
  simp only [Machine.currentFrame, setLocal_stack]
  cases m.stack with
  | nil => rfl
  | cons fid rest => rw [setLocal_eq_setAt]; exact setAt_cref m x w _ fid

theorem currentFrame_setLocal_defmod (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).currentFrame.defmod = m.currentFrame.defmod := by
  simp only [Machine.currentFrame, setLocal_stack]
  cases m.stack with
  | nil => rfl
  | cons fid rest => rw [setLocal_eq_setAt]; exact setAt_defmod m x w _ fid

theorem currentFrame_setLocal_defVis (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).currentFrame.defVis = m.currentFrame.defVis := by
  simp only [Machine.currentFrame, setLocal_stack]
  cases m.stack with
  | nil => rfl
  | cons fid rest => rw [setLocal_eq_setAt]; exact setAt_defVis m x w _ fid

theorem currentFrame_setLocal_captured (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).currentFrame.captured = m.currentFrame.captured := by
  simp only [Machine.currentFrame, setLocal_stack]
  cases m.stack with
  | nil => rfl
  | cons fid rest => rw [setLocal_eq_setAt]; exact setAt_captured m x w _ fid

@[simp] theorem framesSize_setLocal (m : Machine) (x : String) (w : Value) :
    (m.setLocal x w).frames.size = m.frames.size := by
  rw [setLocal_eq_setAt]; exact setAt_framesSize m x w _

end Ratchet.Denote
