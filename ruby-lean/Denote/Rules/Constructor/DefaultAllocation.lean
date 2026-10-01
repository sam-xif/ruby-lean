import Denote.Rules.Constructor.ConstructorState
import Denote.Rules.Constructor.DefaultNew
import Denote.Rules.Primitive.PrimitiveStep
import Ratchet.Guards.NilFields

/-! Default plain allocation preserves the whole caller and returns an empty instance.
This is the builtin's contract, not permission to skip an actual user initializer. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private theorem no_payload_ancestor {h : Heap} {k j : ObjId} (hc : PlainAllocator h k)
    (hj : (Builtins.payloadCoreClasses.contains j || j == Boot.exceptionId) = true) :
    (ancestors h k).contains j = false := by
  cases he : (ancestors h k).contains j with
  | false => rfl
  | true =>
    have hn := List.any_eq_false.mp hc.noPayload j (List.contains_iff_mem.mp he)
    rw [hj] at hn
    exact False.elim (hn rfl)

theorem newImpl_default_step {κ : Ctx} {Γ : Env} {I J : Ty} {m : Machine} {k : ObjId} {cn : String}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) (hn : classNamed? m.heap cn = some k)
    (hk : m.kont = []) (hj : nilFieldsB J = true) :
    StepSpec m Γ (.inst cn J) (builtinStep (Builtins.newImpl m (.ref k) [])) κ I := by
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
        · exact stepSpec_defaultAllocated hm hc hn hk hj

#print axioms newImpl_default_step
end Ratchet.Denote.Typed
