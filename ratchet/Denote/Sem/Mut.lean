import Denote.Sem.State

/-!
# `Denote/Sem/Mut.lean` — the transport for an **instance-variable write**

`Ext` is the transport for an *allocation*: the heap only grew and every old object reads back
identically. That is what `denM`'s `.inst` and `clos` arms need, and it is why `Ext` pins
`Heap.get`.

An ivar write is not an `Ext`. It is the first machine change on this ladder that **mutates an
existing object**, and it needs its own relation, because exactly one thing about the heap
moved: some objects' `ivars` lists. Everything else — the size, and every object's class,
eigenclass, payload and frozen bit — is where it was, and that is what the twenty
heap-shaped components of `StateOk` actually read.

## Why it is a separate relation rather than a weaker `Ext`

`Ext` cannot be weakened to cover this: `denM_ext`'s `.inst` arm reads `ivarOf`, and its `clos`
arm reads the captured frame's locals, so both need `get` in full. The two relations divide the
work the way the components divide: `Mut` transports everything that reads the heap's *shape*,
and the two components that read an object's *contents* — `EnvOk` and `SelfSpineOk` — are
handled at the rung, where the assignment's own guard (`found-issues.md` §F17's
`ivarStaleFree`) is available.

So this file is deliberately **not** a `StateOk_mut`: it is `MutOk`, the eighteen components
that travel, and the rung composes it with the two that do not.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **The heap changed only in some objects' instance variables.** -/
structure Mut (m m₂ : Machine) : Prop where
  frames : m₂.frames = m.frames
  stack : m₂.stack = m.stack
  globals : m₂.globals = m.globals
  size : m₂.heap.objs.size = m.heap.objs.size
  klass : ∀ o, (m₂.heap.get o).klass = (m.heap.get o).klass
  eigen : ∀ o, (m₂.heap.get o).eigen = (m.heap.get o).eigen
  payloadObj : ∀ o, (m₂.heap.get o).payload = (m.heap.get o).payload
  frozen : ∀ o, (m₂.heap.get o).frozen = (m.heap.get o).frozen

theorem Mut.refl (m : Machine) : Mut m m where
  frames := rfl
  stack := rfl
  globals := rfl
  size := rfl
  klass _ := rfl
  eigen _ := rfl
  payloadObj _ := rfl
  frozen _ := rfl

/-! ## The derived heap facts

Everything `StateOk`'s heap-shaped components read, shown to agree — so each component's
transport below is a rewrite rather than an argument. -/

theorem Mut.classPayload {m m₂ : Machine} (h : Mut m m₂) (k : ObjId) :
    m₂.heap.classPayload? k = m.heap.classPayload? k := by
  simp only [Heap.classPayload?, h.payloadObj k]

theorem Mut.shapeAgree {m m₂ : Machine} (h : Mut m m₂) : RubyCore.Proof.ShapeAgree m.heap m₂.heap :=
  fun k => by rw [h.classPayload k]

theorem Mut.ancestors {m m₂ : Machine} (h : Mut m m₂) (hsat : RubyCore.Proof.Saturated m.heap) (k : ObjId) :
    RubyCore.ancestors m₂.heap k = RubyCore.ancestors m.heap k :=
  (RubyCore.Proof.ancestors_congr_grow h.shapeAgree (by rw [h.size]; exact Nat.le_refl _)
    hsat k).symm ▸ rfl

theorem Mut.classOf {m m₂ : Machine} (h : Mut m m₂) (v : Value) :
    RubyCore.classOf m₂.heap v = RubyCore.classOf m.heap v := by
  cases v with
  | ref o => simp only [RubyCore.classOf, h.eigen o, h.klass o]
  | int _ | flt _ | sym _ | nil => rfl
  | bool b => cases b <;> rfl

theorem Mut.realClassOf {m m₂ : Machine} (h : Mut m m₂) (v : Value) :
    RubyCore.realClassOf m₂.heap v = RubyCore.realClassOf m.heap v := by
  cases v with
  | ref o => simp only [RubyCore.realClassOf, h.klass o]
  | int _ | flt _ | sym _ | nil => rfl
  | bool b => cases b <;> rfl

theorem Mut.constLookupEq {m m₂ : Machine} (h : Mut m m₂) (n : String) :
    constLookup m₂.heap n = constLookup m.heap n := by
  simp only [constLookup, h.classPayload Boot.objectId]

theorem Mut.classNamedEq {m m₂ : Machine} (h : Mut m m₂) (n : String) :
    classNamed? m₂.heap n = classNamed? m.heap n := by
  simp only [classNamed?]
  rw [h.constLookupEq n]
  cases constLookup m.heap n with
  | none => rfl
  | some w => cases w <;> simp only [h.classPayload]

theorem Mut.methodOn {m m₂ : Machine} (h : Mut m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (k : ObjId) (n : String) :
    Interp.methodOn m₂.heap k n = Interp.methodOn m.heap k n := by
  unfold Interp.methodOn
  rw [h.ancestors hsat k]
  simp only [h.classPayload]

theorem Mut.isA {m m₂ : Machine} (h : Mut m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (v : Value) (k : ObjId) : RubyCore.isA m₂.heap v k = RubyCore.isA m.heap v k := by
  unfold RubyCore.isA
  rw [h.classOf v, h.ancestors hsat]

theorem Mut.isANameEq {m m₂ : Machine} (h : Mut m m₂) (hsat : RubyCore.Proof.Saturated m.heap)
    (v : Value) (n : String) : isAName m₂.heap v n = isAName m.heap v n := by
  unfold isAName
  rw [h.classNamedEq n]
  cases classNamed? m.heap n with
  | none => rfl
  | some k => exact h.isA hsat v k

theorem Mut.isExactInstEq {m m₂ : Machine} (h : Mut m m₂) (v : Value) (n : String) :
    isExactInst m₂.heap v n = isExactInst m.heap v n := by
  unfold isExactInst
  rw [h.classNamedEq n]
  cases classNamed? m.heap n with
  | none => rfl
  | some k => cases v <;> simp only [h.klass, h.eigen, h.size]

theorem Mut.isClassRefNamedEq {m m₂ : Machine} (h : Mut m m₂) (v : Value) (n : String) :
    isClassRefNamed m₂.heap v n = isClassRefNamed m.heap v n := by
  simp only [isClassRefNamed]
  rw [h.classNamedEq n]

theorem Mut.currentFrame {m m₂ : Machine} (h : Mut m m₂) :
    m₂.currentFrame = m.currentFrame := by
  unfold Machine.currentFrame
  rw [h.stack, h.frames]

theorem Mut.getLocal_go {m m₂ : Machine} (h : Mut m m₂) (x : String) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.getLocal.go m₂ x fid fuel = Machine.getLocal.go m x fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [Machine.getLocal.go, h.frames]
    split
    · rfl
    · split
      · exact ih _
      · rfl

theorem Mut.getLocal {m m₂ : Machine} (h : Mut m m₂) (x : String) :
    m₂.getLocal x = m.getLocal x := by
  simp only [Machine.getLocal, h.stack, h.frames]
  exact h.getLocal_go x _ _

#print axioms Mut.refl
#print axioms Mut.methodOn
#print axioms Mut.isExactInstEq

end Ratchet.Denote
