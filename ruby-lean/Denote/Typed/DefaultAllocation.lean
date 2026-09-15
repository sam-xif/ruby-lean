import Denote.Typed.ConstructorState
import Denote.Typed.PrimitiveStep

/-! Default plain allocation preserves the whole caller and returns an empty instance.
This is the builtin's contract, not permission to skip an actual user initializer. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def defaultAllocated (m : Machine) (k : ObjId) : Machine :=
  { m with heap := pushHeap m.heap { klass := k } }

theorem defaultAllocated_ext {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : ObjId}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) : Ext m (defaultAllocated m k) :=
  ext_push { klass := k } hm.sat hm.core.basicSelf (by intro c; cases c; simp) rfl rfl hc.rooted

theorem defaultAllocated_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : ObjId}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) : StateOk κ Γ I (defaultAllocated m k) :=
  StateOk_ext hm (defaultAllocated_ext hm hc)
    (stringPayloadOk_push hm.stringPayload (by simpa using hc.notString))
    (arrayPayloadOk_push hm.arrayPayload (by simp)) (hashPayloadOk_push hm.hashPayload (by simp)) rfl

theorem defaultAllocated_receiver {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : ObjId} {cn : String}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) (hn : classNamed? m.heap cn = some k) :
    denM (.inst cn .ivar0) (defaultAllocated m k) (.ref m.heap.objs.size) := by
  have he := defaultAllocated_ext hm hc
  rw [denM]
  simp only [isExactInst, he.classNamed?_eq, hn]
  simp [defaultAllocated, pushHeap_get_self, denSpineFrom]

theorem stepSpec_defaultAllocated {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : ObjId} {cn : String}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) (hn : classNamed? m.heap cn = some k)
    (hk : m.kont = []) :
    StepSpec m Γ (.inst cn .ivar0)
      (.next (Interp.withCtl (defaultAllocated m k) (.value (.ref m.heap.objs.size)))) κ I := by
  have hs := defaultAllocated_state hm hc
  have hd := defaultAllocated_receiver hm hc hn
  have hf := Framed.of_ext (defaultAllocated_ext hm hc)
  have h := RunSpec.answer (a := .val (.ref m.heap.objs.size))
    (show ResultOk m Γ (.inst cn .ivar0) _ _ κ I from ⟨hf, hd, fun _ hv => by cases hv; exact hs⟩)
  simpa only [StepSpec, defaultAllocated, Interp.withCtl, deliverA, Answer.ctl, reCtl, hk] using h

private theorem no_payload_ancestor {h : Heap} {k j : ObjId} (hc : PlainAllocator h k)
    (hj : (Builtins.payloadCoreClasses.contains j || j == Boot.exceptionId) = true) :
    (ancestors h k).contains j = false := by
  cases he : (ancestors h k).contains j with
  | false => rfl
  | true =>
    have hn := List.any_eq_false.mp hc.noPayload j (List.contains_iff_mem.mp he)
    rw [hj] at hn
    exact False.elim (hn rfl)

theorem newImpl_default_step {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : ObjId} {cn : String}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) (hn : classNamed? m.heap cn = some k)
    (hk : m.kont = []) :
    StepSpec m Γ (.inst cn .ivar0) (builtinStep (Builtins.newImpl m (.ref k) [])) κ I := by
  obtain ⟨cp, hp, hmod⟩ := hc.payload
  have hcp : m.heap.classPayload? k = some cp := by simp [Heap.classPayload?, hp]
  unfold Builtins.newImpl
  simp only [hcp, hmod, Bool.false_eq_true, ↓reduceIte,
    no_payload_ancestor hc (j := Boot.exceptionId) (by decide),
    no_payload_ancestor hc (j := Boot.stringId) (by decide),
    no_payload_ancestor hc (j := Boot.arrayId) (by decide),
    no_payload_ancestor hc (j := Boot.hashId) (by decide)]
  split
  · trivial
  · split
    · trivial
    · simp only [beq_eq_false_iff_ne.mpr hc.notClass, beq_eq_false_iff_ne.mpr hc.notModule,
        Bool.false_eq_true, ↓reduceIte]
      split
      · trivial
      · split
        · trivial
        · exact stepSpec_defaultAllocated hm hc hn hk

#print axioms newImpl_default_step
end Ratchet.Denote.Typed
