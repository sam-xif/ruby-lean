import Denote.Sem.BuiltinsCapRun

/-!
# `Denote/Sem/StepInterp.lean` — the interpreter's side of the locals layer

`Denote/Sem/StepLocal.lean` states the per-step target (`Step b m m'`) and gives it the three
composites a machine change with no heap in it needs: `Step.frameOnly`, `Step.pop`,
`Step.setLocal`. `Denote/Sem/BuiltinsCapRun.lean` adds `Step.builtins`. This file adds the two
that the *interpreter*'s own arms need and the `Builtins` layer never did, because a builtin
pushes no frame and `evalExpr` does:

* **`Step.alloc`** — an arm that allocates. Stated over **`CapAt`** (`BuiltinsCap.lean`) rather
  than over `Sealed.alloc`'s two `ReachesB` premises, because `CapAt` is the predicate the
  `cap_free` closers already discharge by a pure term, one per payload iota cannot reduce. Every
  allocation in `evalExpr` but the closure literal is capture-free by its constructor.
* **`Step.push_free`** — an arm that pushes a frame capturing nothing. Four of the model's six
  `frames.push` sites default `captured` to `none` (ordinary method frames and class bodies), so
  those close with no side condition at all. The two that set it — `callClosure` from a
  `Closure` and `enterUserMethod` from a `MethodDef` — are exactly what `Sealed`'s `clos` and
  `meth` clauses are *for*, and they get their own lemma below with the heap fact as a
  hypothesis.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **An arm that allocates a capture-free object.** The premise is `CapAt`, so the closers in
`BuiltinsCap.lean` (`cap_free`: `exact hc` / `capAt_proc_none` / `capAt_emptyCore` /
`capAt_cls_nil`) discharge it unchanged. -/
theorem Step.alloc {b : FrameId} {m : Machine} (h : StepInv b m) {obj : Object}
    (hcf : ∀ p, ¬ CapAt obj p) : Step b m { m with heap := (m.heap.alloc obj).2 } := by
  refine ⟨rfl, ?_⟩
  refine { sealed := ?_, wf := ?_, inRange := h.inRange }
  · refine h.sealed.alloc obj (fun cl hp p hcap => ?_) (fun cp hp n md hmd p hcap => ?_)
    · exact absurd (by simp only [CapAt, hp]; exact hcap) (hcf p)
    · exact absurd (by simp only [CapAt, hp]; exact ⟨n, md, hmd, hcap⟩) (hcf p)
  · refine h.wf.alloc obj (fun cl hp p hcap => ?_) (fun cp hp n md hmd p hcap => ?_)
    · exact absurd (by simp only [CapAt, hp]; exact hcap) (hcf p)
    · exact absurd (by simp only [CapAt, hp]; exact ⟨n, md, hmd, hcap⟩) (hcf p)

/-- **An arm that pushes a frame capturing nothing** — the four `frames.push` sites that default
`captured` to `none`. Both of `Sealed.push`'s premises are quantified over the captured id, so a
`none` discharges them vacuously; this is the same shape the L266 `Option` repair gave
`Sealed.clos`. -/
theorem Step.push_free {b : FrameId} {m : Machine} (h : StepInv b m) (fr : RubyCore.Frame)
    (hfr : fr.captured = none) :
    Step b m { m with frames := m.frames.push fr, stack := m.frames.size :: m.stack } := by
  refine ⟨LocalsOff.push h.inRange, ?_⟩
  refine { sealed := ?_, wf := ?_, inRange := ?_ }
  · exact h.sealed.push h.wf h.inRange fr
      (fun p hp => absurd (hfr ▸ hp) (by simp)) (fun p hp => absurd (hfr ▸ hp) (by simp))
  · exact h.wf.push fr (fun p hp => absurd (hfr ▸ hp) (by simp))
  · show b < (m.frames.push fr).size
    simp only [Array.size_push]
    exact Nat.lt_succ_of_lt h.inRange

/-- **…and one that pushes a frame captured from a `Closure` in the heap** — `callClosure`'s
push, which is the case `Sealed.clos` exists for. The closure is supplied as a heap fact, so the
premise is a lookup rather than a claim about `b`. -/
theorem Step.push_clos {b : FrameId} {m : Machine} (h : StepInv b m) (fr : RubyCore.Frame)
    {o : ObjId} {cl : Closure} (hcl : procClosure? m.heap (.ref o) = some cl)
    (hfr : fr.captured = cl.captured) :
    Step b m { m with frames := m.frames.push fr, stack := m.frames.size :: m.stack } := by
  refine ⟨LocalsOff.push h.inRange, ?_⟩
  refine { sealed := ?_, wf := ?_, inRange := ?_ }
  · exact h.sealed.push h.wf h.inRange fr
      (fun p hp => h.wf.clos o cl hcl p (hfr ▸ hp))
      (fun p hp => h.sealed.clos o cl hcl p (hfr ▸ hp))
  · exact h.wf.push fr (fun p hp => h.wf.clos o cl hcl p (hfr ▸ hp))
  · show b < (m.frames.push fr).size
    simp only [Array.size_push]
    exact Nat.lt_succ_of_lt h.inRange

/-- **…and from a `MethodDef` installed in the heap** — `enterUserMethod`'s push, which is the
case the L267 `meth` clause exists for. Together with `push_free` and `push_clos` this covers all
six `frames.push` sites in the model. -/
theorem Step.push_meth {b : FrameId} {m : Machine} (h : StepInv b m) (fr : RubyCore.Frame)
    {k : ObjId} {n : String} {md : MethodDef} (hmd : methodIn m.heap k n = some md)
    (hfr : fr.captured = md.capturedFrame) :
    Step b m { m with frames := m.frames.push fr, stack := m.frames.size :: m.stack } := by
  refine ⟨LocalsOff.push h.inRange, ?_⟩
  refine { sealed := ?_, wf := ?_, inRange := ?_ }
  · exact h.sealed.push h.wf h.inRange fr
      (fun p hp => h.wf.meth k n md hmd p (hfr ▸ hp))
      (fun p hp => h.sealed.meth k n md hmd p (hfr ▸ hp))
  · exact h.wf.push fr (fun p hp => h.wf.meth k n md hmd p (hfr ▸ hp))
  · show b < (m.frames.push fr).size
    simp only [Array.size_push]
    exact Nat.lt_succ_of_lt h.inRange

/-! ## Keyed composites, one per helper `evalExpr` actually calls

`notes.md`'s shape problem: Lean collapses nested record updates into one flat literal, so a
machine that *is* `withCtl m c` does not unify with a lemma stated about `{ ?m with ctl := ?c }`.
The fix there was a keyed variant per callee, and it is the fix here — an arm that ends in
`withCtl` closes by `exact Step.withCtl h _`, with no unification against a machine-sized term.

`raiseErr` is the one that is not just a `ctl` write: it **allocates** the exception object
first, so it is `Step.alloc` (an `.exc` payload, capture-free by its constructor) composed with
the `ctl` change. -/

theorem Step.withCtl {b : FrameId} {m : Machine} (h : StepInv b m) (c : Ctl) :
    Step b m (Interp.withCtl m c) := Step.frameOnly h rfl rfl rfl

theorem Step.withKont {b : FrameId} {m : Machine} (h : StepInv b m) (c : Ctl) (k : Kont) :
    Step b m (Interp.withKont m c k) := Step.frameOnly h rfl rfl rfl

theorem Step.allocStr {b : FrameId} {m : Machine} (h : StepInv b m) (str : String) :
    Step b m (Builtins.allocStr m str).2 := Step.alloc h (fun _ hc => hc)

theorem Step.allocStrEnc {b : FrameId} {m : Machine} (h : StepInv b m) (str : String) (bin : Bool) :
    Step b m (Builtins.allocStrEnc m str bin).2 := Step.alloc h (fun _ hc => hc)

theorem Step.allocArr {b : FrameId} {m : Machine} (h : StepInv b m) (xs : Array Value) :
    Step b m (Builtins.allocArr m xs).2 := Step.alloc h (fun _ hc => hc)

theorem Step.allocHsh {b : FrameId} {m : Machine} (h : StepInv b m)
    (xs : Array (Value × Value)) : Step b m (Builtins.allocHsh m xs).2 :=
  Step.alloc h (fun _ hc => hc)

theorem Step.allocExc {b : FrameId} {m : Machine} (h : StepInv b m) (cls : ObjId) (msg : String) :
    Step b m (Builtins.allocExc m cls msg).2 := Step.alloc h (fun _ hc => hc)

/-- `raiseErr` allocates the exception and then writes `ctl`. -/
theorem Step.raiseErr {b : FrameId} {m : Machine} (h : StepInv b m) (cls : ObjId) (msg : String) :
    Step b m (Interp.raiseErr m cls msg) :=
  let s := Step.allocExc h cls msg
  s.trans (Step.frameOnly s.2 rfl rfl rfl)

/-! ### …and the same keyed composites as **peels**

An arm rarely ends at `withCtl m c`: it ends at `withCtl m₂ c` where `m₂` is what an earlier
part of the same arm produced (`matchGlobal`'s global write, an allocation, a frame push). So
each composite also needs a form that takes `Step b m mid` and extends it.

**These peel, where `MCap`'s did not.** `MCap.push_trans_eq` could not recover its intermediate
machine because `?mid` appeared only under a projection (`?mid.heap.objs`); here `mid` is an
*argument* of the keyed callee (`withCtl mid c`), so the goal determines it first-order and a
`repeat` fixpoint over these closes a chain of any length. -/

theorem Step.withCtl' {b : FrameId} {m mid : Machine} (s : Step b m mid) (c : Ctl) :
    Step b m (Interp.withCtl mid c) := s.trans (Step.withCtl s.2 c)

theorem Step.withKont' {b : FrameId} {m mid : Machine} (s : Step b m mid) (c : Ctl) (k : Kont) :
    Step b m (Interp.withKont mid c k) := s.trans (Step.withKont s.2 c k)

theorem Step.raiseErr' {b : FrameId} {m mid : Machine} (s : Step b m mid) (cls : ObjId)
    (msg : String) : Step b m (Interp.raiseErr mid cls msg) := s.trans (Step.raiseErr s.2 cls msg)

theorem Step.allocStr' {b : FrameId} {m mid : Machine} (s : Step b m mid) (str : String) :
    Step b m (Builtins.allocStr mid str).2 := s.trans (Step.allocStr s.2 str)

theorem Step.allocStrEnc' {b : FrameId} {m mid : Machine} (s : Step b m mid) (str : String)
    (bin : Bool) : Step b m (Builtins.allocStrEnc mid str bin).2 :=
  s.trans (Step.allocStrEnc s.2 str bin)

theorem Step.allocArr' {b : FrameId} {m mid : Machine} (s : Step b m mid) (xs : Array Value) :
    Step b m (Builtins.allocArr mid xs).2 := s.trans (Step.allocArr s.2 xs)

theorem Step.allocHsh' {b : FrameId} {m mid : Machine} (s : Step b m mid)
    (xs : Array (Value × Value)) : Step b m (Builtins.allocHsh mid xs).2 :=
  s.trans (Step.allocHsh s.2 xs)

theorem Step.allocExc' {b : FrameId} {m mid : Machine} (s : Step b m mid) (cls : ObjId)
    (msg : String) : Step b m (Builtins.allocExc mid cls msg).2 :=
  s.trans (Step.allocExc s.2 cls msg)

theorem Step.setLocal' {b : FrameId} {m mid : Machine} (s : Step b m mid) (x : String)
    (w : Value) : Step b m (mid.setLocal x w) := s.trans (Step.setLocal s.2 x w)

theorem Step.push_free' {b : FrameId} {m mid : Machine} (s : Step b m mid) (fr : RubyCore.Frame)
    (hfr : fr.captured = none) :
    Step b m { mid with frames := mid.frames.push fr, stack := mid.frames.size :: mid.stack } :=
  s.trans (Step.push_free s.2 fr hfr)

/-- The generic peel for a machine change the seal cannot see at all: same frames, same stack,
same heap. Stated with the three equations as hypotheses so it is `rfl`-checked per arm. -/
theorem Step.frameOnly' {b : FrameId} {m mid m₂ : Machine} (s : Step b m mid)
    (hs : m₂.stack = mid.stack) (hf : m₂.frames = mid.frames) (hh : m₂.heap = mid.heap) :
    Step b m m₂ := s.trans (Step.frameOnly s.2 hs hf hh)

#print axioms Step.withCtl
#print axioms Step.withCtl'
#print axioms Step.raiseErr
#print axioms Step.alloc
#print axioms Step.push_free
#print axioms Step.push_clos
#print axioms Step.push_meth

end Ratchet.Denote
