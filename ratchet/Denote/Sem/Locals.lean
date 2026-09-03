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

/-! ## The chain runs *downhill*, and that is what makes the fuel irrelevant

`Machine.getLocal` walks with `m.frames.size + 1` fuel, so two machines whose frame arrays have
different sizes walk with different fuel — and an activation grows the array. Comparing the two
walks therefore needs the fuel to stop mattering, which needs the chain to be finite, which is
not a fact about the *types*: `Frame.captured` is an arbitrary `Option FrameId` and nothing in
`RubyCore/Machine.lean` forbids a cycle.

`CaptureDown` is the fact that makes it finite, and it is true of the interpreter for a mundane
reason: a frame captures a frame that already existed, and frames are appended, so the captured
id is *smaller*. Stated here rather than assumed, because it is destined to be a `StateOk`
component — every producer of a machine has to keep it, and the ones that only rewrite a
frame's `locals` (`setLocal`, the `asgnK` arms) keep it for free. -/

/-- **A frame captures an older frame.** -/
def CaptureDown (m : Machine) : Prop :=
  ∀ fid p, (m.frames.getD fid default).captured = some p → p < fid

/-- With the chain running downhill, `getLocal`'s walk is done after `fid` steps, so any two
fuels above that agree. Strong induction on `fid`, which is what "downhill" buys. -/
theorem getLocal_go_fuel_irrel {m : Machine} {x : String} (hcd : CaptureDown m) :
    ∀ (fid : FrameId), ∀ (n₁ n₂ : Nat), fid < n₁ → fid < n₂ →
      Machine.getLocal.go m x fid n₁ = Machine.getLocal.go m x fid n₂ := by
  intro fid
  induction fid using Nat.strongRecOn with
  | _ fid ih =>
    intro n₁ n₂ h₁ h₂
    cases n₁ with
    | zero => exact absurd h₁ (Nat.not_lt_zero _)
    | succ k₁ =>
    cases n₂ with
    | zero => exact absurd h₂ (Nat.not_lt_zero _)
    | succ k₂ =>
      rw [Machine.getLocal.go, Machine.getLocal.go]
      cases hf : (m.frames.getD fid default).locals.find? (·.1 == x) with
      | some p => rfl
      | none =>
        cases hc : (m.frames.getD fid default).captured with
        | none => rfl
        | some p =>
          have hp : p < fid := hcd fid p hc
          exact ih p hp k₁ k₂ (Nat.lt_of_lt_of_le hp (Nat.le_of_lt_succ h₁))
            (Nat.lt_of_lt_of_le hp (Nat.le_of_lt_succ h₂))

/-! ## …so a walk over unchanged frames answers the same thing

The form the run-level statement will be consumed at: two machines, the same stack, and every
frame **on the chain** reading back the same. Nothing is asked about the frames off it, which is
the point — an activation appends frames and rewrites its own, and neither is on the caller's
chain. -/

theorem getLocal_go_congr {m m₂ : Machine} {x : String} :
    ∀ (fuel : Nat) (fid : FrameId),
      (∀ f, ReachesB m f fid fuel = true → m₂.frames.getD f default = m.frames.getD f default) →
      Machine.getLocal.go m₂ x fid fuel = Machine.getLocal.go m x fid fuel
  | 0, _, _ => rfl
  | fuel + 1, fid, hagree => by
    have hhead : m₂.frames.getD fid default = m.frames.getD fid default :=
      hagree fid (reachesB_head m fid fuel)
    rw [Machine.getLocal.go, Machine.getLocal.go, hhead]
    cases hf : (m.frames.getD fid default).locals.find? (·.1 == x) with
    | some p => rfl
    | none =>
      cases hc : (m.frames.getD fid default).captured with
      | none => rfl
      | some p =>
        simp only []
        exact getLocal_go_congr fuel p
          (fun f hr => hagree f (reachesB_step hc hr))

/-- **The lemma the layer is for.** -/
theorem getLocal_congr {m m₂ : Machine} {x : String} (hs : m₂.stack = m.stack)
    (_hcd : CaptureDown m) (hcd₂ : CaptureDown m₂)
    (hlt : m.stack.headD 0 < m.frames.size) (hlt₂ : m.stack.headD 0 < m₂.frames.size)
    (hagree : ∀ f, ReachesB m f (m.stack.headD 0) (m.frames.size + 1) = true →
      m₂.frames.getD f default = m.frames.getD f default) :
    m₂.getLocal x = m.getLocal x := by
  rw [Machine.getLocal, Machine.getLocal, hs]
  -- both walks are run at the *same* fuel first, then each is moved to its own
  rw [getLocal_go_fuel_irrel (x := x) hcd₂ (m.stack.headD 0) (m₂.frames.size + 1)
        (m.frames.size + 1) (Nat.lt_succ_of_lt hlt₂) (Nat.lt_succ_of_lt hlt)]
  exact getLocal_go_congr _ _ hagree

#print axioms getLocal_congr

/-! ## `ReachesB`'s two congruences

Both are needed before the invariant below can be *stated* usefully, because the invariant
quantifies `ReachesB` at the fuel `m.frames.size + 1` and an activation grows that size.

* **Fuel** — irrelevant above `fid`, for `getLocal`'s reason and by the same induction.
* **The machine** — `ReachesB` reads only `captured`, so it does not move when a step rewrites a
  frame's `locals` or appends new frames. That is what makes the invariant survive `setLocal`
  and a frame push without any argument about *which* frame was written. -/

theorem reachesB_fuel_irrel {m : Machine} {b : FrameId} (hcd : CaptureDown m) :
    ∀ (fid : FrameId), ∀ (n₁ n₂ : Nat), fid < n₁ → fid < n₂ →
      ReachesB m b fid n₁ = ReachesB m b fid n₂ := by
  intro fid
  induction fid using Nat.strongRecOn with
  | _ fid ih =>
    intro n₁ n₂ h₁ h₂
    cases n₁ with
    | zero => exact absurd h₁ (Nat.not_lt_zero _)
    | succ k₁ =>
    cases n₂ with
    | zero => exact absurd h₂ (Nat.not_lt_zero _)
    | succ k₂ =>
      rw [ReachesB, ReachesB]
      cases hc : (m.frames.getD fid default).captured with
      | none => rfl
      | some p =>
        simp only []
        have hp : p < fid := hcd fid p hc
        rw [ih p hp k₁ k₂ (Nat.lt_of_lt_of_le hp (Nat.le_of_lt_succ h₁))
          (Nat.lt_of_lt_of_le hp (Nat.le_of_lt_succ h₂))]

theorem reachesB_captured_congr {m m₂ : Machine} {b : FrameId}
    (hcap : ∀ f, (m₂.frames.getD f default).captured = (m.frames.getD f default).captured) :
    ∀ (fuel : Nat) (fid : FrameId), ReachesB m₂ b fid fuel = ReachesB m b fid fuel
  | 0, _ => rfl
  | fuel + 1, fid => by
    rw [ReachesB, ReachesB, hcap fid]
    cases hc : (m.frames.getD fid default).captured with
    | none => rfl
    | some p => simp only []; rw [reachesB_captured_congr hcap fuel p]

/-! ## The seal

`Sealed b m` is the invariant an activation carries, and the sixteenth stall point is the reason
it has a **second** conjunct. The first says the obvious thing — no frame the machine can make
current has `b` on its chain — and on its own it is not preserved: invoking a closure makes the
*closure's* captured frame current, so a closure that captured a chain through `b` reopens it.
That is the falsifier, stated as a clause.

Not stated: anything about `m.kont`. A continuation carries frame *ids* to restore, and
restoring one only pops back to a frame already on the stack, which the first clause covers. -/

structure Sealed (b : FrameId) (m : Machine) : Prop where
  /-- No frame on the activation stack reaches `b`. -/
  stack : ∀ fid ∈ m.stack, ReachesB m b fid (m.frames.size + 1) = false
  /-- …and no closure in the heap captured a chain through `b`. -/
  clos : ∀ (o : ObjId) (cl : Closure), procClosure? m.heap (.ref o) = some cl →
    ReachesB m b cl.captured (m.frames.size + 1) = false

/-- The seal implies what the write lemma above wants, at the current frame. -/
theorem not_reachesFrame_of_sealed {b : FrameId} {m : Machine} (h : Sealed b m)
    (hne : m.stack ≠ []) : ¬ ReachesFrame m b := by
  intro hr
  have hmem : m.stack.headD 0 ∈ m.stack := by
    cases hs : m.stack with
    | nil => exact absurd hs hne
    | cons a rest => simp [hs]
  rw [ReachesFrame, h.stack _ hmem] at hr
  exact absurd hr (by simp)

#print axioms not_reachesFrame_of_sealed
#print axioms reachesB_fuel_irrel

end Ratchet.Denote
