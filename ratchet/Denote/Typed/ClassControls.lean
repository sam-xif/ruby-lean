import Denote.Typed.ClassEntry
import Denote.Sanity

/-! Fresh-class controls. They establish actual entry and heap facts, not acceptance of
the still-gated 061 program. In particular, no method signature stands in for a body proof. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine)

#guard classReadyB bootMachine.heap

-- Both needed facts are checked, not consequences of ancestor-fuel saturation.
private def uncachedObject : Heap :=
  bootMachine.heap.set Boot.objectId { bootMachine.heap.get Boot.objectId with eigen := none }
#guard !classReadyB uncachedObject

-- A fresh object's eigenclass can mask a dangling `klass` at dispatch. Thus old-object
-- agreement plus `freshBasic` alone cannot preserve `ChainsIn`.
private def badFresh (h : Heap) : Object :=
  { klass := h.objs.size + 2, eigen := some Boot.basicObjectId }

example (h : Heap) : classOf (pushHeap h (badFresh h)) (.ref h.objs.size) =
    Boot.basicObjectId := by simp only [classOf, pushHeap_get_self, badFresh]

theorem fresh_dispatch_can_hide_bad_klass (h : Heap) :
    ¬ Proof.ChainsIn (pushHeap h (badFresh h)) := by
  intro hc
  have hk := hc.klass h.objs.size (by simp)
  rw [pushHeap_get_self, pushHeap_size] at hk
  change h.objs.size + 2 < h.objs.size + 1 at hk
  omega

-- Exercise the actual boot entry; no fixed class id is baked into the theorem.
theorem boot_class_entry (hb : bootOkB = true) {name : String} {body : Ratchet.Expr}
    (hn : constOwn bootMachine.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ e, Interp.stepFn (evalFrom bootMachine (.class' name none body)) =
        .next (freshClsMachine (evalFrom bootMachine (.class' name none body)) Boot.objectId
          bootMachine.currentFrame.cref name name e (toRuby body)) ∧
      ClassReady (freshClsHeap bootMachine.heap Boot.objectId name name e) ∧
      classNamed? (freshClsHeap bootMachine.heap Boot.objectId name name e) name =
        some bootMachine.heap.objs.size := by
  have hm := stateOk_boot hb
  obtain ⟨e, he, hs⟩ := stepFn_class_fresh (body := body) hm rfl hn hne
  have ho := hm.core.classReady.chains.boot.2.2.2.2
  exact ⟨e, hs, hm.core.classReady.freshClass ho he,
    classNamed_freshClass ((hm.runtime rfl).classLive) ho⟩

-- Independent execution check of both fresh chains, registration, and the pushed frame.
#guard match Interp.enterClassBody bootMachine "Point" false none .nil with
  | .next n =>
      n.heap.objs.size == bootMachine.heap.objs.size + 2 && classReadyB n.heap &&
      classNamed? n.heap "Point" == some bootMachine.heap.objs.size &&
      (match n.currentFrame.self with | .ref k => k == bootMachine.heap.objs.size | _ => false) &&
      n.currentFrame.defmod == bootMachine.heap.objs.size &&
      n.currentFrame.kind == .classBody &&
      ancestors n.heap bootMachine.heap.objs.size ==
        bootMachine.heap.objs.size :: ancestors bootMachine.heap Boot.objectId &&
      ancestors n.heap (bootMachine.heap.objs.size + 1) ==
        (bootMachine.heap.objs.size + 1) :: ancestors bootMachine.heap
          ((bootMachine.heap.get Boot.objectId).eigen.getD Boot.classId)
  | _ => false

#print axioms boot_class_entry
#print axioms fresh_dispatch_can_hide_bad_klass
end Ratchet.Denote.Typed
