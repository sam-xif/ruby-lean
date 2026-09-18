import Denote.Rules.Init.InitReturn
import Denote.Sem.Core.Alloc

/-! Publication controls, not a constructor typing rule: allocation, a real uncaptured
method frame, two writes, then frame return. Values range over all Integers. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def pairFrame (m : Machine) (k : ObjId) (x y : Int) : RubyCore.Frame :=
  { self := .ref m.heap.objs.size, defmod := k, cref := [k], kind := .method,
    meth := "initialize", locals := [("x", .int x), ("y", .int y)] }
private def pairEntry (m : Machine) (k : ObjId) (x y : Int) : Machine :=
  pushMethodFrame { m with heap := pushHeap m.heap { klass := k } } (pairFrame m k x y)
private def pairWritten (m : Machine) (k : ObjId) (x y : Int) : Machine :=
  Interp.bindIvar (Interp.bindIvar (pairEntry m k x y) "@x" (.int x)) "@y" (.int y)

private theorem pairEntry_self (m : Machine) (k : ObjId) (x y : Int) :
    (pairEntry m k x y).currentFrame.self = .ref m.heap.objs.size := by
  simp [pairEntry, pushMethodFrame, Machine.currentFrame, pairFrame,
    Array.getD_eq_getD_getElem?]

theorem fresh_pair_growth {m : Machine} {k : ObjId} (x y : Int)
    (hsat : Proof.Saturated m.heap)
    (hb : ancestors m.heap Boot.basicObjectId = [Boot.basicObjectId])
    (hk : (ancestors m.heap k).contains Boot.basicObjectId = true) :
    InitGrow m.heap (pairWritten m k x y).heap := by
  have hg := (ext_push (m := m) { klass := k } hsat hb (by intro c; cases c; simp)
    rfl rfl hk).initGrow
  have he : InitGrow m.heap (pairEntry m k x y).heap := hg
  have hw := he.bindIvar (pairEntry_self m k x y) (Nat.le_refl _) "@x" (.int x)
  exact hw.bindIvar (by simp [pairEntry_self]) (Nat.le_refl _) "@y" (.int y)

theorem fresh_pair_publication {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) {k : ObjId}
    (hk : (ancestors m.heap k).contains Boot.basicObjectId = true) (x y : Int) :
    Framed m (popMethodFrame (pairWritten m k x y)) := by
  have hf : FramePres (pushMethodFrame m (pairFrame m k x y)) (pairWritten m k x y) :=
    .of_eq (by simp [pairWritten, pairEntry, pushMethodFrame])
      (by simp [pairWritten, pairEntry, pushMethodFrame])
  exact initializer_pop_framed hm.frameInRange.2 rfl
    (by simp [pairWritten, pairEntry, pushMethodFrame]) hf
    (fresh_pair_growth x y hm.sat hm.core.basicSelf hk)

private theorem pairWritten_object (m : Machine) (k : ObjId) (x y : Int) :
    (pairWritten m k x y).heap.get m.heap.objs.size =
      ({ klass := k, ivars := [("@y", .int y), ("@x", .int x)] } : Object) := by
  unfold pairWritten
  rw [bindIvar_get_self (by simp [pairEntry_self])
    (by simp [bindIvar_size, pairEntry, pushMethodFrame])]
  rw [bindIvar_get_self (pairEntry_self m k x y) (by simp [pairEntry, pushMethodFrame])]
  simp [pairEntry, pushMethodFrame, pushHeap_get_self]

/-- The newly published result gets the initialized shape, not its earlier nil slots. -/
theorem fresh_pair_result {m : Machine} {k : ObjId} {cn : String} (x y : Int)
    (hsat : Proof.Saturated m.heap)
    (hb : ancestors m.heap Boot.basicObjectId = [Boot.basicObjectId])
    (hk : (ancestors m.heap k).contains Boot.basicObjectId = true)
    (hn : classNamed? m.heap cn = some k) :
    denM (.inst cn (.ivarCons "@x" .int (.ivarCons "@y" .int .ivar0)))
      (popMethodFrame (pairWritten m k x y)) (.ref m.heap.objs.size) := by
  have hg := fresh_pair_growth x y hsat hb hk
  have hc := hg.classNamed?_eq cn
  simp only [denM, denSpineFrom, isExactInst, popMethodFrame, hc, hn,
    pairWritten_object, ivarOf]
  simp [pairWritten, bindIvar_size, pairEntry, pushMethodFrame, isIntV]

theorem fresh_pair_first_step (m : Machine) (k : ObjId) (x y : Int) :
    Interp.stepFn { pairEntry m k x y with ctl := .value (.int x), kont := [.asgnK .ivar "@x"] } =
      .next { Interp.bindIvar (pairEntry m k x y) "@x" (.int x) with ctl := .value (.int x), kont := [] } :=
  stepFn_ivarWrite (pairEntry_self m k x y)
    (by simp [pairEntry, pushMethodFrame, pushHeap_get_self])

theorem fresh_pair_second_step (m : Machine) (k : ObjId) (x y : Int) :
    Interp.stepFn { Interp.bindIvar (pairEntry m k x y) "@x" (.int x) with
      ctl := .value (.int y), kont := [.asgnK .ivar "@y"] } =
      .next { pairWritten m k x y with ctl := .value (.int y), kont := [] } :=
  stepFn_ivarWrite (o := m.heap.objs.size) (by simp [pairEntry_self]) (by
    rw [(bindIvar_ivarOnly (pairEntry m k x y) "@x" (.int x)).frozen]
    simp [pairEntry, pushMethodFrame, pushHeap_get_self])

-- The old relation cannot express this publication: it forbids all fresh ivars.
example (m : Machine) (k : ObjId) (x y : Int) :
    ¬ Ext m (popMethodFrame (pairWritten m k x y)) := by
  intro he
  have hv := he.freshIvars m.heap.objs.size (Nat.le_refl _)
  simp [popMethodFrame, pairWritten_object] at hv

-- The general publication lemma is inhabited at the actual prelude boot, too.
example (hb : bootOkB = true) (x y : Int) :
    Framed bootMachine (popMethodFrame (pairWritten bootMachine Boot.basicObjectId x y)) := by
  have hm := stateOk_boot hb
  exact fresh_pair_publication hm (by rw [hm.core.basicSelf]; rfl) x y

#print axioms fresh_pair_publication
#print axioms fresh_pair_result
#print axioms fresh_pair_first_step
#print axioms fresh_pair_second_step
end Ratchet.Denote.Typed
