import Denote.Sem.FrameLocal

/-!
# `Denote/Sem/StepLocal.lean` — the `Interp` layer of the locality claim

`Denote/Sem/FrameLocal.lean` proved the `Builtins` layer, where the claim is uniform: a builtin
that answers with a value leaves every frame's locals alone. The interpreter is where that stops
being true — it *does* write `frames`, at exactly four sites (`Machine.setLocal`,
`setCurrentFrame`, `setLastMatchValue`, and six `frames.push`es) — so the claim here is the
weaker, parameterised one `Denote/Sem/Locals.lean` was built for: **a frame off the current
capture chain reads its locals back unchanged.**

`b` is that frame, and the two hypotheses are exactly what the four writers need:

* `¬ ReachesFrame m b` — `setLocal`'s target is on the chain it starts from
  (`reachesB_setLocal_target`), so a frame off the chain is not it, and `setCurrentFrame`'s
  target is the chain's head;
* `b < m.frames.size` — a `push` writes past the end, and *at* the end `getD` stops answering
  `default`.

`setLastMatchValue` needs neither: it copies `locals`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

/-- **`b`'s locals, unchanged.** The weakening of `LocalsSame` the interpreter satisfies. -/
def LocalsOff (b : FrameId) (m m' : Machine) : Prop :=
  (m'.frames.getD b default).locals = (m.frames.getD b default).locals

theorem LocalsOff.refl (b : FrameId) (m : Machine) : LocalsOff b m m := rfl

theorem LocalsOff.trans {b : FrameId} {a c d : Machine} (h₁ : LocalsOff b a c)
    (h₂ : LocalsOff b c d) : LocalsOff b a d := by
  unfold LocalsOff at h₁ h₂ ⊢; rw [h₂, h₁]

theorem LocalsSame.off {b : FrameId} {m m' : Machine} (h : LocalsSame m m') :
    LocalsOff b m m' := h.2 b

/-- A push writes past the end, so a frame already in range is untouched. -/
theorem LocalsOff.push {b : FrameId} {m : Machine} {fr : RubyCore.Frame} {st : List FrameId}
    (hlt : b < m.frames.size) :
    LocalsOff b m { m with frames := m.frames.push fr, stack := st } := by
  unfold LocalsOff
  show ((m.frames.push fr).getD b default).locals = _
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]

/-- …and `setLocal` writes on the chain, which `b` is off. -/
theorem LocalsOff.setLocal {b : FrameId} {m : Machine} {x : String} {w : Value}
    (h : ¬ ReachesFrame m b) : LocalsOff b m (m.setLocal x w) :=
  locals_setLocal_of_not_reaches h

#print axioms LocalsOff.push

/-! ## What the first attempt at `unwind` measured, and what it changes

`unwind` was attempted with the `Builtins` layer's automation and three more leaf closers (the
three ways the interpreter can leave `b` alone: frames untouched, a frame pushed past `b`, a
local written on a chain `b` is off). It closes all but **four** arms, and those four name the
four helpers `unwind` hands off to: `forStep`, `callClosure`, `finishRegion`, `nextClause`.

That is not the interesting part. The interesting part is what the fourth of them shows about
the *statement*: `callClosure` is reached at `{ m with stack := m.stack.tail }`, and

> `¬ ReachesFrame m b` does not survive a stack pop.

`ReachesFrame` reads the chain from `m.stack.headD 0`, so popping makes a *different* frame
current — and if `b` is the frame being returned to, it is now on the chain. Which is exactly
the end of an activation, and exactly why `Denote/Sem/Locals.lean`'s `Sealed` quantifies over
**every** frame on the stack rather than over the current one. So the per-step claim has to be
stated with `Sealed b m`, not `¬ ReachesFrame m b`, and its conclusion has to carry `Sealed b m'`
onward for the run-level induction to compose.

Carrying `Sealed b m'` is where the interpreter layer stops being automation: for each of the
six `frames.push`es it needs "the new frame's chain misses `b`" (free for a method frame, whose
`captured` is `none`; a *fact about the closure* for a block frame), and for each closure
allocation it needs "the new closure's captured chain misses `b`". Those two are the closure
premise the sixteenth stall point identifies, arriving where it was predicted to.

So the next step is not more arms: it is `Sealed`'s preservation lemmas — `Sealed.pop`,
`Sealed.push_method`, `Sealed.push_block`, `Sealed.alloc_closure` — and the `ClosuresOk`
exactness component they need. The vocabulary above is what they will be stated over.
-/

/-! ## The composites

One lemma per machine change, pairing the locals claim with the invariant so an arm of the
interpreter closes with a single `exact`. These are what the interpreter walk is stated over. -/

/-- `Step b m m'`: the step left `b`'s locals alone and handed the invariant back. -/
def Step (b : FrameId) (m m' : Machine) : Prop := LocalsOff b m m' ∧ StepInv b m'

theorem Step.refl {b : FrameId} {m : Machine} (h : StepInv b m) : Step b m m :=
  ⟨LocalsOff.refl b m, h⟩

theorem Step.trans {b : FrameId} {a c d : Machine} (h₁ : Step b a c) (h₂ : Step b c d) :
    Step b a d := ⟨h₁.1.trans h₂.1, h₂.2⟩

/-- Everything that is not the frames, the stack or the heap. -/
theorem Step.frameOnly {b : FrameId} {m m₂ : Machine} (h : StepInv b m)
    (hs : m₂.stack = m.stack) (hf : m₂.frames = m.frames) (hh : m₂.heap = m.heap) :
    Step b m m₂ :=
  ⟨by unfold LocalsOff; rw [hf],
   { sealed := h.sealed.frameOnly hs hf hh
     wf := h.wf.frameOnly hs hf hh
     inRange := by rw [hf]; exact h.inRange }⟩

theorem Step.pop {b : FrameId} {m : Machine} (h : StepInv b m) (hne : m.stack.tail ≠ []) :
    Step b m { m with stack := m.stack.tail } :=
  ⟨rfl, { sealed := h.sealed.pop, wf := h.wf.pop hne, inRange := h.inRange }⟩

theorem Step.setLocal {b : FrameId} {m : Machine} (h : StepInv b m) (x : String) (w : Value) :
    Step b m (m.setLocal x w) :=
  ⟨LocalsOff.setLocal (not_reachesFrame_of_sealed h.sealed h.wf.nonEmpty),
   { sealed := h.sealed.setLocal x w
     wf := h.wf.setLocal x w
     inRange := by
       rw [show (m.setLocal x w).frames.size = m.frames.size from by
         show (m.frames.set! _ _).size = _
         simp [Array.set!]]
       exact h.inRange }⟩


/-! ## The seal is **not** preserved by `Builtins.run` — measured, not predicted

`Denote/Sem/FrameLocal.lean` proved the `Builtins` layer uniform for `LocalsSame`, and the
plan above reads as though the seal came with it: a builtin writes no frame, so `Sealed`
should travel across `Builtins.run` for free. It does not, and the reason is a single
builtin.

`Symbol#to_proc` (`RubyCore/Builtins/Strings.lean` L441) *allocates a closure*:

```lean
let cl : Closure :=
  { params := [.req "__recv", .rest (some "__rest")], locals := [],
    body := .send (some (.var .lvar "__recv")) s [.splat (some (.var .lvar "__rest"))] none,
    captured := 0, home := 0, lam := true }
```

`captured := 0` — the **toplevel frame**, because a `Closure`'s `captured` is a `FrameId` and
not an `Option FrameId`, so there is no way to spell "captures nothing" and `0` is the
inert choice. `Sealed`'s `clos` clause reads exactly that field, so the allocation puts a
closure over frame `0` into the heap and the seal at `b = 0` is gone. `Sealed.alloc`'s premise
(`∀ cl, obj.payload = .proc cl → ReachesB m b cl.captured … = false`) is therefore **false**
at the one `b` the toplevel narrowing rungs are about.

Three things follow, and the third is the design consequence.

1. **It is not a soundness bug in the model.** The closure's body is
   `__recv.s(*__rest)` — a fixed, assignment-free expression — so invoking it cannot write a
   local of frame `0`. `Sealed` is a *sufficient* condition for "`b`'s locals are stable" and
   this is a place where it is strictly stronger than the truth.
2. **It is not repairable by strengthening `Sealed.alloc`.** The allocation really happens, at
   a machine the seal really holds at, so no premise stated over `(b, m)` can exclude it. What
   distinguishes the `to_proc` closure from a dangerous one is its *body*.
3. **So the frame graph is not enough.** The invariant the layer needs cannot be a predicate on
   `frames` alone; the closure clause has to be able to say "…or this closure cannot write",
   which is a syntactic condition on `cl.body`. That is `Ctx.closures`' exactness component
   (`StateOk`'s `ClosuresOk`, still `trivial`) arriving from the direction the sixteenth stall
   point predicted, with **one escape it did not name**: a closure that no `Judge` rule and no
   prelude line created, but a *builtin* did.

Stated as a `Prop` with a name and refuted, for the reason `Denote/Sem/Frame.lean`'s
`KontFrame` was: a comment saying "the seal probably travels" would still be a comment. -/

/-- **What the plan wanted**: the `Builtins` layer preserves the seal outright. -/
def BuiltinsSeal : Prop :=
  ∀ (b : FrameId) (bid : String) (recv : Value) (args : List Value) (m : Machine),
    Sealed b m → FramesWF m → b < m.frames.size →
    ∀ v m', Builtins.run bid recv args m = .ok v m' → Sealed b m'

/-- The smallest machine at which the seal says anything: two frames, neither capturing, the
*caller*'s (`0`) sealed off behind the frame that is running (`1`), and an empty heap. -/
def toProcM : Machine :=
  { ctl := .value .nil, kont := [], stack := [1],
    frames := #[default, default], heap := ⟨#[]⟩ }

theorem toProcM_frame : ∀ f : FrameId, toProcM.frames.getD f default = default
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => by
      show (#[(default : RubyCore.Frame), default]).getD (n + 2) default = default
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp)]
      rfl

theorem toProcM_captured (f : FrameId) : (toProcM.frames.getD f default).captured = none := by
  rw [toProcM_frame f]; rfl

theorem toProcM_noProc (o : ObjId) (cl : Closure) :
    procClosure? toProcM.heap (.ref o) = some cl → False := by
  intro h
  rw [procClosure?] at h
  rw [show (toProcM.heap.get o) = default from by
    show (Array.getD #[] o default) = default
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp)]; rfl] at h
  rw [show (default : Object).payload = Payload.none from rfl] at h
  exact absurd h (by simp)

theorem sealed_toProcM : Sealed 0 toProcM where
  stack := by
    intro fid hmem
    have : fid = 1 := by simpa [toProcM] using hmem
    subst this
    rw [ReachesB, toProcM_captured]
    rfl
  clos := fun o cl h => absurd h (fun hc => toProcM_noProc o cl hc)

theorem framesWF_toProcM : FramesWF toProcM := by
  refine { down := ?_, nonEmpty := ?_, stack := ?_, clos := ?_ }
  · intro fid p hc; rw [toProcM_captured] at hc; exact absurd hc (by simp)
  · simp [toProcM]
  · intro fid hmem
    have : fid = 1 := by simpa [toProcM] using hmem
    subst this
    show 1 < (#[(default : RubyCore.Frame), default]).size
    simp
  · intro o cl h; exact absurd h (fun hc => toProcM_noProc o cl hc)

/-- The probe: `Symbol#to_proc` at `toProcM` answers with a closure whose captured chain
reaches frame `0`. A `Bool` and a `#guard` rather than a `decide`, for `Denote/Sanity.lean`'s
reason — this is a build gate, and `native_decide` would cost an axiom. -/
def toProcBreaksB : Bool :=
  match Builtins.run "Symbol#to_proc" (.sym "f") [] toProcM with
  | .ok v m' =>
      match procClosure? m'.heap v with
      | some cl => ReachesB m' 0 cl.captured (m'.frames.size + 1)
      | none => false
  | _ => false

#guard toProcBreaksB

/-- **`BuiltinsSeal` is refutable.** -/
theorem not_BuiltinsSeal (hb : toProcBreaksB = true) : ¬ BuiltinsSeal := by
  intro h
  rw [toProcBreaksB] at hb
  split at hb
  · rename_i v m' heq
    have hs := h 0 "Symbol#to_proc" (.sym "f") [] toProcM sealed_toProcM framesWF_toProcM
      (by show 0 < (#[(default : RubyCore.Frame), default]).size; simp) v m' heq
    split at hb
    · rename_i cl hcl
      cases v with
      | ref o => rw [hs.clos o cl hcl] at hb; exact absurd hb (by simp)
      | _ => exact absurd hcl (by simp [procClosure?])
    · exact absurd hb (by simp)
  · exact absurd hb (by simp)

#print axioms not_BuiltinsSeal

end Ratchet.Denote

