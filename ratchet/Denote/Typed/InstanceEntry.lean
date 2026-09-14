import Denote.Typed.MethodState
import Denote.Typed.InstanceRead
import Ratchet.ClassCtx

/-! Moving open receiver fields into an ordinary method activation. This supplies the
self-spine premise from the receiver's type; it does not assume complete outgoing StateOk. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem selfSpine_open_of_instance {m : Machine} {cn : String} {I : Ty}
    (h : denM (.inst cn I) m m.currentFrame.self) : SelfSpineOk I m false := by
  rw [denM] at h
  exact ⟨h.2, by intro _ _ hf; cases hf⟩

theorem instance_required_spine {m : Machine} {recv : Value} {cn name : String}
    {I : Ty} (md : MethodDef) (names : List String) (args : List Value)
    (hi : FirstOrder I = true) (hv : denM (.inst cn I) m recv) :
    SelfSpineOk I (pushMethodFrame m (requiredFrame recv name md names args)) false := by
  have hv' : denM (.inst cn I) (pushMethodFrame m (requiredFrame recv name md names args)) recv :=
    (denM_heap_only (τ := .inst cn I) (m₁ := m)
      (m₂ := pushMethodFrame m (requiredFrame recv name md names args)) hi rfl).mp hv
  apply selfSpine_open_of_instance (cn := cn)
  simpa only [currentFrame_pushMethodFrame, requiredFrame] using hv'

theorem instance_required_self {m : Machine} {recv : Value} {fr : Ratchet.Frame}
    {κ : Ctx} {I : Ty} (md : MethodDef) (names : List String) (args : List Value)
    (hi : FirstOrder I = true) (hv : denM (.inst fr.recvClass I) m recv) :
    SelfTyOk (instanceBodyCtx κ fr I).selfTy
      (pushMethodFrame m (requiredFrame recv fr.methName md names args)) := by
  change denM (.inst fr.recvClass I) _ _
  rw [currentFrame_pushMethodFrame]
  exact (denM_heap_only (τ := .inst fr.recvClass I) (m₁ := m)
    (m₂ := pushMethodFrame m (requiredFrame recv fr.methName md names args)) hi rfl).mp hv

#print axioms instance_required_spine
#print axioms instance_required_self
end Ratchet.Denote.Typed
