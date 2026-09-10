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

#print axioms Step.alloc
#print axioms Step.push_free
#print axioms Step.push_clos
#print axioms Step.push_meth

end Ratchet.Denote
