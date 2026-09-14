import Denote.Typed.ClassEntry
import Denote.Sem.ClassHeap
import Denote.Typed.ClassQueryControls
import Denote.Typed.ClassCoreControls
import Denote.Typed.ClassFrameControls
import Denote.Typed.ClassBaseControls
import Denote.Typed.ClassNameControls
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
  exact ⟨e, hs, hm.core.classReady.freshClass hm.sat ho he,
    classNamed_freshClass ((hm.runtime rfl).classLive) ho⟩

/-- The class heap change preserves the full caller contract, including nested snapshots.
This is heap publication with unchanged frames, not execution of the class body. -/
theorem boot_class_publication (hb : bootOkB = true) {name : String} {e : ObjId}
    (hn : constOwn bootMachine.heap Boot.objectId name = none)
    (he : (bootMachine.heap.get Boot.objectId).eigen = some e) :
    Framed bootMachine { bootMachine with
      heap := freshClsHeap bootMachine.heap Boot.objectId name name e } :=
  .of_freshClass (stateOk_boot hb) hn he rfl rfl (.of_eq rfl rfl)

example (hb : bootOkB = true) {name cn : String} {e : ObjId} {v : Value}
    (hn : constOwn bootMachine.heap Boot.objectId name = none)
    (he : (bootMachine.heap.get Boot.objectId).eigen = some e)
    (hv : denM (.arrayOf (.inst cn (.ivarCons "@x" .int .ivar0))) bootMachine v) :
    denM (.arrayOf (.inst cn (.ivarCons "@x" .int .ivar0)))
      { bootMachine with heap := freshClsHeap bootMachine.heap Boot.objectId name name e } v :=
  (boot_class_publication hb hn he).firstOrder _ rfl v hv

/-- Registration must be fresh. Force the composite to overwrite String (not the actual
Ruby reopen branch), and preservation of its old nominal meaning is false. -/
theorem rebinding_string_breaks_data (hb : bootOkB = true) (e : ObjId) :
    ¬ DataPres bootMachine.heap
      (freshClsHeap bootMachine.heap Boot.objectId "String" "String" e) := by
  intro hp
  have hm := stateOk_boot hb
  have ho := hm.core.classReady.chains.boot.2.2.2.2
  have hn := classNamed_freshClass (name := "String") (e := e) ((hm.runtime rfl).classLive) ho
  have hold := hp.named "String" Boot.stringId hm.core.stringNamed
  rw [hn] at hold
  have hlt : Boot.stringId < bootMachine.heap.objs.size :=
    Nat.lt_of_le_of_lt (by decide : Boot.stringId ≤ Boot.procId) hm.core.classReady.chains.boot.2.2.2.1
  exact (Nat.ne_of_lt hlt) (Option.some.inj hold).symm

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
#print axioms boot_class_publication
#print axioms rebinding_string_breaks_data
#print axioms fresh_dispatch_can_hide_bad_klass
end Ratchet.Denote.Typed
