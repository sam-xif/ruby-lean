import Denote.Sem.Mut

/-!
# `Denote/Sem/Locals.lean` — the capture chain, and what a write can reach

The first brick of the layer `Denote/Sem/notes.md`'s fifteenth and **sixteenth** stall points
describe. The sixteenth is the one that shapes this file: the fifteenth's plan named the
statement "a callee's run leaves the caller's frame's locals alone", and that statement is
**false** —

```ruby
x = 1
f = lambda { x = 2 }
def g(p); p.call; end
g(f)                      # x is 2, confirmed under CRuby
```

— because `Machine.setLocal` walks the **capture chain**, not the frame stack. A callee only
has to get its hands on a closure that captured its caller, and an argument will do.

What is true, and what this file starts, is the same statement with the closures named:

> a run leaves frame `b`'s locals alone **provided `b` is not on the capture chain of any frame
> the run makes current, and no closure the run can reach captures a chain through `b`**

and the *first* half of that is decided by exactly one function — `Machine.setLocal`'s `owner`
walk. So that is what is proved here: the walk's answer is always either its `start` or a frame
on the chain it is walking, so a write from a machine whose chain misses `b` cannot touch `b`,
and `b`'s locals read back unchanged.

## Why the chain is spelled as a `Bool` with explicit fuel

`Machine.setLocal.owner` and `Machine.getLocal.go` are both fuel-bounded walks over `m.frames`
(a `partial def` would be opaque to the kernel — `RubyCore/Machine.lean`), called with
`m.frames.size + 1`. `ReachesB` mirrors that shape rather than being an inductive relation,
for the reason `Denote/Val.lean`'s predicates are `Bool`s: the eventual consumer is a `StateOk`
component, and a component that can be *computed* at the booted machine is one
`Denote/Sanity.lean` can measure.

## What is **not** here yet

The second half — the closure condition, and the per-step induction carrying it through
`stepFn` — is the rest of the layer. This file is the part that can be proved without any of
that machinery, and it is the part every later piece calls: the reason a callee's activation
is safe is not that it is a callee, it is that `b` is off its chain.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **`b` is on the capture chain starting at `fid`**, walked with `fuel` steps.

`fid` itself counts: the chain includes its own head, because `setLocal`'s `owner` may answer
the frame it started from — both when that frame owns the name and as its `start` default. -/
def ReachesB (m : Machine) (b : FrameId) : FrameId → Nat → Bool
  | _, 0 => false
  | fid, fuel + 1 =>
    fid == b || (match (m.frames.getD fid default).captured with
                 | some p => ReachesB m b p fuel
                 | none => false)

/-- The chain from the *current* frame, at the fuel every walk in `RubyCore/Machine.lean`
uses. -/
def ReachesFrame (m : Machine) (b : FrameId) : Prop :=
  ReachesB m b (m.stack.headD 0) (m.frames.size + 1) = true

theorem reachesB_head (m : Machine) (b : FrameId) (fuel : Nat) :
    ReachesB m b b (fuel + 1) = true := by
  rw [ReachesB]; simp

theorem reachesB_step {m : Machine} {b fid p : FrameId} {fuel : Nat}
    (hc : (m.frames.getD fid default).captured = some p)
    (h : ReachesB m b p fuel = true) : ReachesB m b fid (fuel + 1) = true := by
  rw [ReachesB, hc]; simp [h]

/-! ## `setLocal`'s target is on the chain

One lemma, and the only place `Machine.setLocal.owner` is unfolded. Stated at arbitrary fuel
and start so the induction has somewhere to go, and as a **disjunction** because the walk has
two ways to end: it finds a frame that owns the name, or it runs off the end of the chain and
falls back to `start`. At the call site the two coincide — `owner` is entered with
`fid = start` — which is what makes the corollary unconditional. -/

theorem owner_start_or_reaches (m : Machine) (x : String) (start : FrameId) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.setLocal.owner m x start fid fuel = start ∨
      ReachesB m (Machine.setLocal.owner m x start fid fuel) fid fuel = true
  | 0, fid => Or.inl rfl
  | fuel + 1, fid => by
    rw [Machine.setLocal.owner]
    by_cases hown : (m.frames.getD fid default).locals.any (·.1 == x) = true
    · rw [if_pos hown]
      exact Or.inr (reachesB_head m fid fuel)
    · rw [if_neg (by simpa using hown)]
      cases hc : (m.frames.getD fid default).captured with
      | none => exact Or.inl rfl
      | some p =>
        simp only []
        rcases owner_start_or_reaches m x start fuel p with h | h
        · exact Or.inl h
        · exact Or.inr (reachesB_step hc h)

/-- **The target of a write is on the chain the write starts from.** -/
theorem reachesB_setLocal_target (m : Machine) (x : String) :
    ReachesB m (Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0)
        (m.frames.size + 1)) (m.stack.headD 0) (m.frames.size + 1) = true := by
  rcases owner_start_or_reaches m x (m.stack.headD 0) (m.frames.size + 1) (m.stack.headD 0)
    with h | h
  · rw [h]; exact reachesB_head _ _ _
  · exact h

/-! ## The consequence: a frame off the chain reads back unchanged

`RubyCore/Proof/HeapFacts.lean` has this for `Object`; the `Frame` flavour is stated here and
generically, since the only thing the proof uses of the element type is `Inhabited`. -/

theorem getD_set!_ne {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (o : α) (h : j ≠ i) :
    (a.set! i o).getD j default = a.getD j default := by
  have hsz : (a.set! i o).size = a.size := by simp [Array.set!]
  by_cases hj : j < a.size
  · simp only [Array.getD]
    rw [dif_pos (hsz ▸ hj), dif_pos hj]
    exact Array.getElem_setIfInBounds_ne hj (Ne.symm h)
  · simp only [Array.getD]
    rw [dif_neg (hsz ▸ hj), dif_neg hj]


theorem frames_setLocal_of_not_reaches {m : Machine} {b : FrameId} {x : String} {w : Value}
    (h : ¬ ReachesFrame m b) :
    (m.setLocal x w).frames.getD b default = m.frames.getD b default := by
  have hne : b ≠ Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0)
      (m.frames.size + 1) := by
    intro heq
    exact h (heq ▸ reachesB_setLocal_target m x)
  show (m.frames.set! _ _).getD b default = _
  exact getD_set!_ne _ _ _ _ hne

/-- …and so does every local it holds, which is the form the run-level induction wants. -/
theorem locals_setLocal_of_not_reaches {m : Machine} {b : FrameId} {x : String} {w : Value}
    (h : ¬ ReachesFrame m b) :
    ((m.setLocal x w).frames.getD b default).locals = (m.frames.getD b default).locals := by
  rw [frames_setLocal_of_not_reaches h]

#print axioms locals_setLocal_of_not_reaches

end Ratchet.Denote
