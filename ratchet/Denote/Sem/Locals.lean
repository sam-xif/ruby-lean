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

theorem getD_set!_self {α : Type} [Inhabited α] (a : Array α) (i : Nat) (o : α)
    (h : i < a.size) : (a.set! i o).getD i default = o := by
  simp [Array.getD, h]

theorem getD_set!_oob {α : Type} [Inhabited α] (a : Array α) (i : Nat) (o : α)
    (h : ¬ i < a.size) : (a.set! i o).getD i default = a.getD i default := by
  have hsz : (a.set! i o).size = a.size := by simp [Array.set!]
  simp only [Array.getD]
  rw [dif_neg (hsz ▸ h), dif_neg h]

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
  /-- …and no closure in the heap captured a chain through `b`.

      Quantified over the captured id rather than projecting it (L266): `Closure.captured`
      is an `Option`, and a closure that captured **nothing** — the `Symbol#to_proc` pair,
      the only source — reaches nothing, so the clause is vacuous there rather than being a
      claim about frame `0`. That is the whole fidelity repair the sixteenth stall point
      needed; the shape is now the same one `Sealed.push` already used for `Frame`. -/
  clos : ∀ (o : ObjId) (cl : Closure), procClosure? m.heap (.ref o) = some cl →
    ∀ p, cl.captured = some p → ReachesB m b p (m.frames.size + 1) = false

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

/-! ## `Sealed`'s preservation, for the machine changes that need no premise

Three of them, and they are the three the interpreter makes most often. The two that *do* need
a premise — pushing a **block** frame and allocating a **closure** — are the closure premise the
sixteenth stall point identifies, and they are not here.

All three come out of one congruence, and the congruence is deliberately weak in the right
place: it asks about `captured` and `size` rather than about the frames array, because
`setLocal` changes a frame's `locals` and the seal does not read those.

The enabling lemma for the *fourth* (a `frames.push`) is a third `ReachesB` congruence: a push
changes the array at the pushed index, so "agree everywhere" fails there — and it does not
matter, because with `CaptureDown` the walk from `fid` never reads an index above `fid`. -/

theorem reachesB_congr_below {m m₂ : Machine} {b : FrameId} (hcd : CaptureDown m)
    (hcap : ∀ f, (m₂.frames.getD f default).captured = (m.frames.getD f default).captured ∨
      ¬ (f < m.frames.size)) :
    ∀ (fuel : Nat) (fid : FrameId), fid < m.frames.size →
      ReachesB m₂ b fid fuel = ReachesB m b fid fuel
  | 0, _, _ => rfl
  | fuel + 1, fid, hlt => by
    have hf : (m₂.frames.getD fid default).captured = (m.frames.getD fid default).captured := by
      rcases hcap fid with h | h
      · exact h
      · exact absurd hlt h
    rw [ReachesB, ReachesB, hf]
    cases hc : (m.frames.getD fid default).captured with
    | none => rfl
    | some p =>
      simp only []
      rw [reachesB_congr_below hcd hcap fuel p (Nat.lt_trans (hcd fid p hc) hlt)]

/-- **The seal's congruence.** Stated over `captured` and `size` rather than over the frames
array, so that a write to a frame's `locals` is one of its instances. -/
theorem Sealed.congr {b : FrameId} {m m₂ : Machine} (h : Sealed b m)
    (hsz : m₂.frames.size = m.frames.size)
    (hcap : ∀ f, (m₂.frames.getD f default).captured = (m.frames.getD f default).captured)
    (hh : ∀ (o : ObjId) (cl : Closure), procClosure? m₂.heap (.ref o) = some cl →
      ∀ p, cl.captured = some p → ReachesB m b p (m.frames.size + 1) = false)
    (hst : ∀ fid ∈ m₂.stack, fid ∈ m.stack) : Sealed b m₂ where
  stack := fun fid hmem => by
    rw [hsz, reachesB_captured_congr hcap]
    exact h.stack fid (hst fid hmem)
  clos := fun o cl hcl p hp => by
    rw [hsz, reachesB_captured_congr hcap]
    exact hh o cl hcl p hp

/-- **Popping the stack.** The frames the seal talks about only shrink. -/
theorem Sealed.pop {b : FrameId} {m : Machine} (h : Sealed b m) :
    Sealed b { m with stack := m.stack.tail } :=
  h.congr rfl (fun _ => rfl) (fun o cl hc => h.clos o cl hc)
    (fun fid hmem => List.mem_of_mem_tail hmem)

/-- **Anything that is not the frames, the stack or the heap** — `ctl`, `kont`, `out`,
`globals`, `currentExc`: the fields the seal does not read. -/
theorem Sealed.frameOnly {b : FrameId} {m m₂ : Machine} (h : Sealed b m)
    (hs : m₂.stack = m.stack) (hf : m₂.frames = m.frames) (hh : m₂.heap = m.heap) :
    Sealed b m₂ :=
  h.congr (by rw [hf]) (fun _ => by rw [hf])
    (fun o cl hc => h.clos o cl (by rw [hh] at hc; exact hc)) (fun fid hmem => hs ▸ hmem)

/-- **A local write.** `setLocal` touches `locals`, and the seal reads `captured`. -/
theorem Sealed.setLocal {b : FrameId} {m : Machine} (h : Sealed b m) (x : String) (w : Value) :
    Sealed b (m.setLocal x w) := by
  have hsz : (m.setLocal x w).frames.size = m.frames.size := by
    show (m.frames.set! _ _).size = _
    simp [Array.set!]
  refine h.congr hsz (fun f => ?_) (fun o cl hc => h.clos o cl hc) (fun fid hmem => hmem)
  show ((m.frames.set! _ _).getD f default).captured = _
  by_cases hf : f = Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0)
      (m.frames.size + 1)
  · by_cases hlt : f < m.frames.size
    · rw [hf, getD_set!_self m.frames _ _ (hf ▸ hlt)]
    · rw [hf, getD_set!_oob m.frames _ _ (fun hc => hlt (hf ▸ hc))]
  · rw [getD_set!_ne m.frames _ f _ hf]

#print axioms Sealed.congr
#print axioms Sealed.setLocal

/-! ## The frame array's well-formedness, and the push

`Sealed.push` needs three facts that are true of the interpreter and are not consequences of
anything above: every id the walk can reach is *in range*. `CaptureDown` is one of them; the
other two are the stack's and the closures'. Bundled, because all three are destined for the
same `StateOk` component and every producer of a machine owes all three at once.

Measurable at the booted machine, which is the test `Denote/Sanity.lean` applies to every
component: the boot machine has one frame, an empty capture chain and no closures. -/

structure FramesWF (m : Machine) : Prop where
  /-- A frame captures an older frame. -/
  down : CaptureDown m
  /-- **There is a current frame.** Not bookkeeping: without it `m.stack.headD 0` is `0`, a
      frame the seal says nothing about, and `setLocal` could write `b` through *its* chain.
      `Denote/Sem/State.lean`'s `FrameInRange` is the same clause one file over. -/
  nonEmpty : m.stack ≠ []
  /-- Every frame on the activation stack exists. -/
  stack : ∀ fid ∈ m.stack, fid < m.frames.size
  /-- …and so does every frame a closure captured — when it captured one at all (L266). -/
  clos : ∀ (o : ObjId) (cl : Closure), procClosure? m.heap (.ref o) = some cl →
    ∀ p, cl.captured = some p → p < m.frames.size

/-- **Pushing a frame.** The seal survives it exactly when the pushed frame's *captured* frame
is one the seal already covers — which is free for a **method** frame, whose `captured` is
`none`, and is a fact about the closure for a **block** frame. That split is the sixteenth stall
point, and this is where it is spent. -/
theorem Sealed.push {b : FrameId} {m : Machine} (h : Sealed b m) (hwf : FramesWF m)
    (hb : b < m.frames.size) (fr : RubyCore.Frame)
    (hin : ∀ p, fr.captured = some p → p < m.frames.size)
    (hcap : ∀ p, fr.captured = some p → ReachesB m b p (m.frames.size + 1) = false) :
    Sealed b { m with frames := m.frames.push fr, stack := m.frames.size :: m.stack } := by
  -- the array agrees with the old one *below* the pushed index, which is all the walk reads
  have hbelow : ∀ f,
      ((m.frames.push fr).getD f default).captured = (m.frames.getD f default).captured ∨
      ¬ (f < m.frames.size) := by
    intro f
    by_cases hf : f < m.frames.size
    · refine Or.inl ?_
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_push_lt hf, Array.getElem?_eq_getElem hf]
    · exact Or.inr hf
  have hsz : ((m.frames.push fr).size) = m.frames.size + 1 := by simp
  refine { stack := ?_, clos := ?_ }
  · intro fid hmem
    show ReachesB _ b fid ((m.frames.push fr).size + 1) = false
    rw [hsz]
    rcases List.mem_cons.mp hmem with hfe | hmem'
    · -- the fresh frame: it is not `b` (which is in range), and its chain is the captured one
      subst hfe
      rw [ReachesB]
      have hne : (m.frames.size == b) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hc => absurd (hc ▸ hb) (Nat.lt_irrefl _)
      rw [hne]
      simp only [Bool.false_or]
      cases hc : ((m.frames.push fr).getD m.frames.size default).captured with
      | none => rfl
      | some p =>
        simp only []
        have hfr : ((m.frames.push fr).getD m.frames.size default) = fr := by
          simp [Array.getD_eq_getD_getElem?, Array.getElem?_push]
        rw [hfr] at hc
        rw [reachesB_congr_below (m := m) hwf.down hbelow _ p (hin p hc)]
        rw [reachesB_fuel_irrel (m := m) hwf.down p (m.frames.size + 1)
          (m.frames.size + 1) (Nat.lt_succ_of_lt (hin p hc)) (Nat.lt_succ_of_lt (hin p hc))]
        exact hcap p hc
    · -- an old stack frame: in range, so the walk never reads the pushed index
      have hlt := hwf.stack fid hmem'
      rw [reachesB_congr_below (m := m) hwf.down hbelow _ fid hlt,
        reachesB_fuel_irrel (m := m) hwf.down fid (m.frames.size + 1 + 1)
          (m.frames.size + 1) (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hlt))
          (Nat.lt_succ_of_lt hlt)]
      exact h.stack fid hmem'
  · intro o cl hcl p hp
    show ReachesB _ b p ((m.frames.push fr).size + 1) = false
    rw [hsz]
    have hlt := hwf.clos o cl hcl p hp
    rw [reachesB_congr_below (m := m) hwf.down hbelow _ p hlt,
      reachesB_fuel_irrel (m := m) hwf.down p (m.frames.size + 1 + 1)
        (m.frames.size + 1) (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hlt))
        (Nat.lt_succ_of_lt hlt)]
    exact h.clos o cl hcl p hp

#print axioms Sealed.push

/-! ### Reading an allocated heap

Three lemmas, one per position relative to the fresh id. `RubyCore/Proof/HeapFacts.lean` has the
`set!` flavours; these are `push`'s. -/

theorem alloc_get_lt {h : Heap} {o : ObjId} (obj : Object) (ho : o < h.objs.size) :
    ((h.alloc obj).2).get o = h.get o := by
  simp only [Heap.alloc, Heap.get]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_push_lt ho, Array.getElem?_eq_getElem ho]

theorem alloc_get_self {h : Heap} (obj : Object) :
    ((h.alloc obj).2).get h.objs.size = obj := by
  simp only [Heap.alloc, Heap.get]
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push]

theorem alloc_get_gt {h : Heap} {o : ObjId} (obj : Object) (ho : ¬ o < h.objs.size)
    (hne : ¬ o = h.objs.size) : ((h.alloc obj).2).get o = default := by
  simp only [Heap.alloc, Heap.get]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_neg hne,
    Array.getElem?_eq_none (Nat.le_of_not_lt ho), Option.getD_none]

/-- **Allocating an object.** The seal survives it unless the object *is* a closure over a
chain through `b` — the other half of the sixteenth stall point's premise, and the half a
syntactic condition can decide: a block literal's captured frame is the frame it is created in.

Built through `Sealed.congr`, whose closure clause is stated at the *old* machine — which is
what lets the fresh id be discharged by the premise while every old id goes through the seal. -/
theorem Sealed.alloc {b : FrameId} {m : Machine} (h : Sealed b m) (obj : Object)
    (hcl : ∀ cl, obj.payload = .proc cl → ∀ p, cl.captured = some p →
      ReachesB m b p (m.frames.size + 1) = false) :
    Sealed b { m with heap := (m.heap.alloc obj).2 } := by
  refine h.congr rfl (fun _ => rfl) (fun o cl hcl' => ?_) (fun fid hmem => hmem)
  rw [procClosure?] at hcl'
  by_cases ho : o < m.heap.objs.size
  · refine h.clos o cl ?_
    rw [procClosure?, ← alloc_get_lt obj ho]
    exact hcl'
  · by_cases hoe : o = m.heap.objs.size
    · rw [hoe, alloc_get_self obj] at hcl'
      split at hcl'
      · rename_i c heq
        injection hcl' with hcl'
        exact hcl' ▸ hcl c heq
      · exact absurd hcl' (by simp)
    · rw [alloc_get_gt obj ho hoe] at hcl'
      rw [show (default : Object).payload = Payload.none from rfl] at hcl'
      exact absurd hcl' (by simp)

#print axioms Sealed.alloc

/-! ## `FramesWF`'s preservation, and the composite invariant

The seal is the interesting half of the run-level invariant; `FramesWF` is the bookkeeping half,
and it has to travel with it because `Sealed.push` consumes it. Same five machine changes, and
each one is one clause at a time.

`StepInv` bundles the three things a step has to be handed and hand back: the seal, the
well-formedness, and `b`'s own in-rangeness (which a `push` preserves and nothing shrinks). -/

theorem FramesWF.pop {m : Machine} (h : FramesWF m) (hne : m.stack.tail ≠ []) :
    FramesWF { m with stack := m.stack.tail } where
  down := h.down
  nonEmpty := hne
  stack := fun fid hmem => h.stack fid (List.mem_of_mem_tail hmem)
  clos := h.clos

theorem FramesWF.frameOnly {m m₂ : Machine} (h : FramesWF m) (hs : m₂.stack = m.stack)
    (hf : m₂.frames = m.frames) (hh : m₂.heap = m.heap) : FramesWF m₂ where
  down := fun fid p hc => h.down fid p (by rw [hf] at hc; exact hc)
  nonEmpty := by rw [hs]; exact h.nonEmpty
  stack := fun fid hmem => by rw [hf]; exact h.stack fid (hs ▸ hmem)
  clos := fun o cl hcl => by rw [hf]; exact h.clos o cl (by rw [hh] at hcl; exact hcl)

theorem FramesWF.setLocal {m : Machine} (h : FramesWF m) (x : String) (w : Value) :
    FramesWF (m.setLocal x w) := by
  have hsz : (m.setLocal x w).frames.size = m.frames.size := by
    show (m.frames.set! _ _).size = _
    simp [Array.set!]
  have hcap : ∀ f, ((m.setLocal x w).frames.getD f default).captured
      = (m.frames.getD f default).captured := by
    intro f
    show ((m.frames.set! _ _).getD f default).captured = _
    by_cases hf : f = Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0)
        (m.frames.size + 1)
    · by_cases hlt : f < m.frames.size
      · rw [hf, getD_set!_self m.frames _ _ (hf ▸ hlt)]
      · rw [hf, getD_set!_oob m.frames _ _ (fun hc => hlt (hf ▸ hc))]
    · rw [getD_set!_ne m.frames _ f _ hf]
  exact { down := fun fid p hc => h.down fid p (by rw [hcap fid] at hc; exact hc)
          nonEmpty := h.nonEmpty
          stack := fun fid hmem => by rw [hsz]; exact h.stack fid hmem
          clos := fun o cl hcl p hp => by rw [hsz]; exact h.clos o cl hcl p hp }

theorem FramesWF.push {m : Machine} (h : FramesWF m) (fr : RubyCore.Frame)
    (hin : ∀ p, fr.captured = some p → p < m.frames.size) :
    FramesWF { m with frames := m.frames.push fr, stack := m.frames.size :: m.stack } := by
  have hsz : ((m.frames.push fr).size) = m.frames.size + 1 := by simp
  have hlt : ∀ f, f < m.frames.size →
      (m.frames.push fr).getD f default = m.frames.getD f default := by
    intro f hf
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_push_lt hf, Array.getElem?_eq_getElem hf]
  have hself : (m.frames.push fr).getD m.frames.size default = fr := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  refine { down := ?_, nonEmpty := by simp, stack := ?_, clos := ?_ }
  · intro fid p hc
    by_cases hf : fid < m.frames.size
    · rw [hlt fid hf] at hc
      exact h.down fid p hc
    · by_cases hfe : fid = m.frames.size
      · rw [hfe, hself] at hc
        exact hfe ▸ hin p hc
      · -- past the end: `default` captures nothing
        rw [show (m.frames.push fr).getD fid default = default from by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_neg hfe,
            Array.getElem?_eq_none (Nat.le_of_not_lt hf), Option.getD_none]] at hc
        rw [show (default : RubyCore.Frame).captured = none from rfl] at hc
        exact absurd hc (by simp)
  · intro fid hmem
    show fid < (m.frames.push fr).size
    rw [hsz]
    rcases List.mem_cons.mp hmem with hfe | hmem'
    · exact hfe ▸ Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (h.stack fid hmem')
  · intro o cl hcl p hp
    show p < (m.frames.push fr).size
    rw [hsz]
    exact Nat.lt_succ_of_lt (h.clos o cl hcl p hp)

theorem FramesWF.alloc {m : Machine} (h : FramesWF m) (obj : Object)
    (hcl : ∀ cl, obj.payload = .proc cl → ∀ p, cl.captured = some p → p < m.frames.size) :
    FramesWF { m with heap := (m.heap.alloc obj).2 } := by
  refine { down := h.down, nonEmpty := h.nonEmpty, stack := h.stack, clos := ?_ }
  intro o cl hcl'
  rw [procClosure?] at hcl'
  by_cases ho : o < m.heap.objs.size
  · refine h.clos o cl ?_
    rw [procClosure?, ← alloc_get_lt obj ho]
    exact hcl'
  · by_cases hoe : o = m.heap.objs.size
    · rw [hoe, alloc_get_self obj] at hcl'
      split at hcl'
      · rename_i c heq
        injection hcl' with hcl'
        exact hcl' ▸ hcl c heq
      · exact absurd hcl' (by simp)
    · rw [alloc_get_gt obj ho hoe] at hcl'
      rw [show (default : Object).payload = Payload.none from rfl] at hcl'
      exact absurd hcl' (by simp)

/-- **What a step is handed and hands back.** -/
structure StepInv (b : FrameId) (m : Machine) : Prop where
  sealed : Sealed b m
  wf : FramesWF m
  inRange : b < m.frames.size

#print axioms FramesWF.push
#print axioms FramesWF.alloc

end Ratchet.Denote
