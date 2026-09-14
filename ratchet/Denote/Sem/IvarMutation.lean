import Denote.Sem.Framed
import RubyCore.Proof.HeapFacts

/-! An initializer really changes its receiver's shape. The old universal first-order
frame cannot describe that effect, even when no source local aliases the receiver. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

/-- Mask only the changed field. Payloads, classes, eigenclasses, and frozen flags survive. -/
theorem bindIvar_data (m : Machine) (x : String) (v : Value) (k : ObjId) :
    { (Interp.bindIvar m x v).heap.get k with ivars := [] } =
      { m.heap.get k with ivars := [] } := by
  unfold Interp.bindIvar
  split
  · rename_i o hs
    simp only [Heap.get, Heap.set]
    by_cases hk : k = o
    · subst k
      by_cases ho : o < m.heap.objs.size
      · rw [Proof.objs_getD_set!_self _ _ _ ho]
      · rw [Proof.objs_getD_set!_oob _ _ _ ho]
    · rw [Proof.objs_getD_set!_ne _ _ _ _ hk]
  · rfl

theorem bindIvar_size (m : Machine) (x : String) (v : Value) :
    (Interp.bindIvar m x v).heap.objs.size = m.heap.objs.size := by
  unfold Interp.bindIvar
  split <;> simp [Heap.set]

theorem bindIvar_ivarOnly (m : Machine) (x : String) (v : Value) :
    Proof.IvarOnly m.heap (Interp.bindIvar m x v).heap :=
  ⟨bindIvar_size m x v,
    fun k => by simpa only using congrArg Object.klass (bindIvar_data m x v k),
    fun k => by simpa only using congrArg Object.eigen (bindIvar_data m x v k),
    fun k => by simpa only using congrArg Object.payload (bindIvar_data m x v k),
    fun k => by simpa only using congrArg Object.frozen (bindIvar_data m x v k)⟩

theorem bindIvar_get_other {m : Machine} {o k : ObjId} {x : String} {v : Value}
    (hs : m.currentFrame.self = .ref o) (hk : k ≠ o) :
    (Interp.bindIvar m x v).heap.get k = m.heap.get k := by
  simp only [Interp.bindIvar, hs, Heap.get, Heap.set]
  exact Proof.objs_getD_set!_ne _ _ _ _ hk

theorem ivarOf_bindIvar_self {m : Machine} {o : ObjId} {x : String} {v : Value}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size) :
    ivarOf (Interp.bindIvar m x v).heap (.ref o) x = v := by
  simp only [Interp.bindIvar, hs, ivarOf, Heap.get, Heap.set]
  rw [Proof.objs_getD_set!_self _ _ _ ho]
  simp

theorem ivarOf_bindIvar_other {m : Machine} {o : ObjId} {x : String} {v w : Value}
    (hs : m.currentFrame.self = .ref o) (hw : w ≠ .ref o) :
    ivarOf (Interp.bindIvar m x v).heap w = ivarOf m.heap w := by
  funext y
  cases w <;> try rfl
  rename_i k
  simp only [ivarOf, bindIvar_get_other (k := k) hs (by intro h; subst k; exact hw rfl)]

/-- This is the real successful assignment transition, not a replacement execution model. -/
theorem stepFn_ivarWrite {m : Machine} {o : ObjId} {x : String} {v : Value} {rest : List Kont}
    (hs : m.currentFrame.self = .ref o) (hf : (m.heap.get o).frozen = false) :
    Interp.stepFn { m with ctl := .value v, kont := .asgnK .ivar x :: rest } =
      .next { Interp.bindIvar m x v with ctl := .value v, kont := rest } := by
  simp only [Interp.stepFn, Interp.applyKont]
  change (match m.currentFrame.self with
    | .ref o => _
    | _ => _) = _
  rw [hs]
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  simp only [Interp.bindIvar, Interp.withCtl]
  change (StepResult.next _) = _
  rw [show ({ m with ctl := .value v, kont := rest } : Machine).currentFrame.self = .ref o from hs]
  rw [hs]

/-- No tactic can prove the existing `Framed` contract for this successful write.
The forbidden old type is first-order but observes the receiver's previous nil slot. -/
theorem nil_ivar_write_not_framed {m : Machine} {o : ObjId} {x cn : String}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size)
    (hc : isExactInst m.heap (.ref o) cn = true)
    (hn : ivarOf m.heap (.ref o) x = .nil) :
    ¬ Framed m (Interp.bindIvar m x (.int 1)) := by
  intro hf
  have hd : denM (.inst cn (.ivarCons x .nilT .ivar0)) m (.ref o) := by
    simp [denM, denSpineFrom, hc, hn, isNilV]
  have hout := hf.firstOrder (.inst cn (.ivarCons x .nilT .ivar0)) rfl (.ref o) hd
  have hv := ivarOf_bindIvar_self (x := x) (v := .int 1) hs ho
  simp only [denM, denSpineFrom, List.not_mem_nil, false_or, and_true] at hout
  have hnil := hout.2
  rw [hv] at hnil
  cases hnil

#print axioms ivarOf_bindIvar_self
#print axioms bindIvar_ivarOnly
#print axioms stepFn_ivarWrite
#print axioms nil_ivar_write_not_framed
end Ratchet.Denote
