/-
Adequacy, determinism, and preservation for the control-core `Step` relation
(`Step.lean`). See `implementation-notes.md` L13 for scope and intent.

- `Step.sound` / `Step.deterministic` live in `Step.lean`.
- `Step.heap_monotone` — a global invariant proved by induction over the step
  relation: the heap only grows (ObjIds never reused, artifact 01 §2). This is
  the concrete shape of the fresh-allocation fact a machine↔SOS representation
  relation depends on.
- `Step.complete` — every executable `.next` transition of a config *in the
  fragment* is realized by `Step`. With `Step.sound` this is function–relation
  adequacy on the slice: `InFrag m → (Step m m' ↔ stepFn m = .next m')`.
-/
import RubyCore.Proof.Step

namespace RubyCore
namespace Proof

open Interp

/-! ## Preservation: the heap only grows -/

/-- Frame updates don't touch the heap. -/
@[simp] theorem setCurrentFrame_heap (m : Machine) (f : Frame) :
    (m.setCurrentFrame f).heap = m.heap := by
  unfold Machine.setCurrentFrame; split <;> rfl

@[simp] theorem setLocal_heap (m : Machine) (x : String) (v : Value) :
    (m.setLocal x v).heap = m.heap := by unfold Machine.setLocal; rfl

@[simp] theorem setGlobal_heap (m : Machine) (x : String) (v : Value) :
    (m.setGlobal x v).heap = m.heap := rfl

/-- `bindIvar` mutates an object in place, so the heap size is unchanged. -/
@[simp] theorem bindIvar_heapSize (m : Machine) (x : String) (v : Value) :
    (bindIvar m x v).heap.objs.size = m.heap.objs.size := by
  unfold bindIvar; split
  · simp [Heap.set, Heap.get]
  · rfl

/-- `raiseErr` allocates one exception object, so the heap grows by one. -/
@[simp] theorem raiseErr_heapSize (m : Machine) (cls : ObjId) (msg : String) :
    (raiseErr m cls msg).heap.objs.size = m.heap.objs.size + 1 := by
  simp [raiseErr, Builtins.allocExc, Heap.alloc]

/-- The heap never shrinks across a step (ObjIds are never reused). -/
theorem Step.heap_monotone {m m' : Machine} (h : Step m m') :
    m.heap.objs.size ≤ m'.heap.objs.size := by
  cases h <;> simp_all [withCtl, withKont, pop] <;> omega

/-! ## Completeness: the fragment -/

/-- Jumps the fragment handles (break/next/redo — the loop jumps; return/raise/
    retry are L1/L2). -/
def FragJump : Jump → Prop
  | .brkJ _ => True
  | .nxtJ _ => True
  | .redoJ => True
  | _ => False

/-- Konts the fragment has rules for. -/
def FragKont : Kont → Prop
  | .seqK _ => True
  | .asgnK .cvar _ => False
  | .asgnK _ _ => True
  | .ifK _ _ => True
  | .whileCondK _ _ => True
  | .whileBodyK _ _ => True
  | .jumpValK .retK => False
  | .jumpValK _ => True
  | _ => False

/-- Expression heads the fragment evaluates (only the head matters per step). -/
def FragExpr : Expr → Prop
  | .int _ | .flt _ | .str _ | .sym _ | .tru | .fls | .nil | .self' => True
  | .var .cvar _ => False
  | .var _ _ => True
  | .vasgn .cvar _ _ => False
  | .vasgn _ _ _ => True
  | .if' _ _ _ => True
  | .while' _ _ => True
  | .dowhile _ _ => True
  | .brk _ => True
  | .nxt _ => True
  | .redo' => True
  | .seq _ => True
  | _ => False

/-- A machine config in the control-core fragment: `self` is an object (always
    true at toplevel), every live kont is a fragment kont, and the control is
    an eval of a fragment head, a value, or a fragment jump. -/
def InFrag (m : Machine) : Prop :=
  (∃ o, m.currentFrame.self = .ref o) ∧
  (∀ k ∈ m.kont, FragKont k) ∧
  (∀ e, m.ctl = .eval e → FragExpr e) ∧
  (∀ j, m.ctl = .jump j → FragJump j)

/-- If some `Step` fires and the executable takes a `.next` step, they agree —
    because `stepFn` is a function (`Step.sound` + `.next` injectivity). Lets
    completeness discharge each case by just *naming the right constructor*. -/
theorem realize {m m' m'' : Machine} (hs : stepFn m = .next m') (hstep : Step m m'') :
    Step m m' := by
  have h : (StepResult.next m' : StepResult) = StepResult.next m'' := hs ▸ hstep.sound
  injection h with h'; subst h'; exact hstep

/-- **Completeness.** Every executable `.next` step of an in-fragment config is
    realized by `Step`. With `Step.sound`, this is function–relation adequacy on
    the fragment: `InFrag m → (Step m m' ↔ stepFn m = .next m')`. -/
theorem Step.complete {m m' : Machine} (hf : InFrag m) (hs : stepFn m = .next m') :
    Step m m' := by
  obtain ⟨⟨o, hself⟩, hkont, hce, hcj⟩ := hf
  rcases hcc : m.ctl with e | v | j
  · -- control = eval e
    have hfe := hce e hcc
    cases e with
    | int n => exact realize hs (.intLit hcc)
    | flt x => exact realize hs (.fltLit hcc)
    | str s => exact realize hs (.strLit hcc)
    | sym s => exact realize hs (.symLit hcc)
    | tru => exact realize hs (.truLit hcc)
    | fls => exact realize hs (.flsLit hcc)
    | nil => exact realize hs (.nilLit hcc)
    | self' => exact realize hs (.selfLit hcc)
    | var k x => cases k with
      | lvar => exact realize hs (.varLvar hcc)
      | gvar => exact realize hs (.varGvar hcc)
      | ivar => exact realize hs (.varIvar hcc hself)
      | cvar => simp [FragExpr] at hfe
    | vasgn k x rhs => cases k with
      | lvar => exact realize hs (.vasgnLvar hcc)
      | ivar => exact realize hs (.vasgnIvar hcc)
      | gvar => exact realize hs (.vasgnGvar hcc)
      | cvar => simp [FragExpr] at hfe
    | if' c t e => exact realize hs (.ifEval hcc)
    | while' c b => exact realize hs (.whileEval hcc)
    | dowhile b c => exact realize hs (.dowhileEval hcc)
    | brk e => cases e with
      | some e => exact realize hs (.brkSome hcc)
      | none => exact realize hs (.brkNone hcc)
    | nxt e => cases e with
      | some e => exact realize hs (.nxtSome hcc)
      | none => exact realize hs (.nxtNone hcc)
    | redo' => exact realize hs (.redoEval hcc)
    | seq es => cases es with
      | nil => exact realize hs (.seqNil hcc)
      | cons e rest => cases rest with
        | nil => exact realize hs (.seqOne hcc)
        | cons a b => exact realize hs (.seqCons hcc)
    | _ => simp [FragExpr] at hfe
  · -- control = value v
    cases hk : m.kont with
    | nil => simp [stepFn, hcc, applyKont, hk] at hs
    | cons k rest =>
      have hfk : FragKont k := hkont k (by rw [hk]; simp)
      cases k with
      | seqK es => cases es with
        | nil => exact realize hs (.seqKNil hcc hk)
        | cons e es => exact realize hs (.seqKCons hcc hk)
      | asgnK kind x => cases kind with
        | lvar => exact realize hs (.asgnKLvar hcc hk)
        | gvar => exact realize hs (.asgnKGvar hcc hk)
        | ivar =>
          -- L2 split on the frozen check `stepFn` now performs for `@x=`
          cases hfr : (m.heap.get o).frozen with
          | false => exact realize hs (.asgnKIvar hcc hk hself hfr)
          | true =>
            cases hins : Builtins.inspectP (pop m rest) (.ref o) with
            | ok r => exact realize hs (.asgnKIvarFrozen hcc hk hself hfr hins)
            | error e =>
              -- impure inspect ⇒ `stepFn` gates (`.unsupported`), so `hs` is absurd
              simp_all [stepFn, applyKont, Machine.currentFrame, pop]
        | cvar => simp [FragKont] at hfk
      | ifK t e => cases hb : v.truthy with
        | true => exact realize hs (.ifKTrue hcc hk hb)
        | false => cases e with
          | some e => exact realize hs (.ifKFalseSome hcc hk hb)
          | none => exact realize hs (.ifKFalseNone hcc hk hb)
      | whileCondK c body => cases hb : v.truthy with
        | true => exact realize hs (.whileCondKTrue hcc hk hb)
        | false => exact realize hs (.whileCondKFalse hcc hk hb)
      | whileBodyK c body => exact realize hs (.whileBodyK hcc hk)
      | jumpValK kind => cases kind with
        | retK => simp [FragKont] at hfk
        | brkK => exact realize hs (.jumpValKBrk hcc hk)
        | nxtK => exact realize hs (.jumpValKNxt hcc hk)
      | _ => simp [FragKont] at hfk
  · -- control = jump j
    have hfj := hcj j hcc
    cases j with
    | brkJ v =>
      cases hk : m.kont with
      | nil => simp [stepFn, hcc, unwind, hk] at hs
      | cons k rest =>
        have hfk : FragKont k := hkont k (by rw [hk]; simp)
        cases k with
        | seqK es => exact realize hs (.unwindPropSeqK hcc hk)
        | asgnK kind x => exact realize hs (.unwindPropAsgnK hcc hk)
        | ifK t e => exact realize hs (.unwindPropIfK hcc hk)
        | jumpValK kind => exact realize hs (.unwindPropJumpValK hcc hk)
        | whileCondK c body => exact realize hs (.unwindWhileCondBrk hcc hk)
        | whileBodyK c body => exact realize hs (.unwindWhileBodyBrk hcc hk)
        | _ => simp [FragKont] at hfk
    | nxtJ v =>
      cases hk : m.kont with
      | nil => simp [stepFn, hcc, unwind, hk] at hs
      | cons k rest =>
        have hfk : FragKont k := hkont k (by rw [hk]; simp)
        cases k with
        | seqK es => exact realize hs (.unwindPropSeqK hcc hk)
        | asgnK kind x => exact realize hs (.unwindPropAsgnK hcc hk)
        | ifK t e => exact realize hs (.unwindPropIfK hcc hk)
        | jumpValK kind => exact realize hs (.unwindPropJumpValK hcc hk)
        | whileCondK c body => exact realize hs (.unwindWhileCondNxt hcc hk)
        | whileBodyK c body => exact realize hs (.unwindWhileBodyNxt hcc hk)
        | _ => simp [FragKont] at hfk
    | redoJ =>
      cases hk : m.kont with
      | nil => simp [stepFn, hcc, unwind, hk] at hs
      | cons k rest =>
        have hfk : FragKont k := hkont k (by rw [hk]; simp)
        cases k with
        | seqK es => exact realize hs (.unwindPropSeqK hcc hk)
        | asgnK kind x => exact realize hs (.unwindPropAsgnK hcc hk)
        | ifK t e => exact realize hs (.unwindPropIfK hcc hk)
        | jumpValK kind => exact realize hs (.unwindPropJumpValK hcc hk)
        | whileCondK c body => exact realize hs (.unwindWhileCondRedo hcc hk)
        | whileBodyK c body => exact realize hs (.unwindWhileBodyRedo hcc hk)
        | _ => simp [FragKont] at hfk
    | retJ v => simp [FragJump] at hfj
    | raiseJ v => simp [FragJump] at hfj
    | retryJ => simp [FragJump] at hfj

/-- **Function–relation adequacy** on the fragment. -/
theorem Step.adequacy {m m' : Machine} (hf : InFrag m) :
    Step m m' ↔ stepFn m = .next m' :=
  ⟨Step.sound, Step.complete hf⟩

end Proof
end RubyCore
