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

end Ratchet.Denote
