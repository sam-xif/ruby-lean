import Denote.Typed.PrimitiveStep

/-! Primitive allocation results: a String value or a checked non-type-error exception. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem stepSpec_string {Γ : Env} {m : Machine} (hm : StateOk ctx0 Γ .ivar0 m)
    (hk : m.kont = []) (s : String) (binary : Bool) :
    StepSpec m Γ (.cls "String") (builtinStep (Builtins.okStrEnc m binary s)) := by
  have he := ext_push (m := m) (strObj s binary) hm.sat hm.core.basicSelf
    (fun c => by simp [strObj]) rfl rfl (by simpa [strObj] using hm.core.stringBasic)
  obtain ⟨hn, hd⟩ := strLit_alloc_ok (Γ := Γ) (m := m) (s := s) [] hm binary
  have hf := (Framed.of_ext he).trans (Framed_reCtl _ (.value (.ref m.heap.objs.size)) [])
  have h := RunSpec.answer (a := .val (.ref m.heap.objs.size))
    (show ResultOk m Γ (.cls "String") _ _ from
      ⟨hf, hd, fun _ hv => by cases hv; exact hn⟩)
  simpa only [StepSpec, builtinStep, Builtins.okStrEnc, Builtins.allocStrEnc,
    Heap.alloc, pushHeap, strObj, Interp.withCtl, deliverA, Answer.ctl, reCtl, hk] using h

theorem stepSpec_error {Γ : Env} {m : Machine} {τ : Ty} {cls : ObjId}
    (hm : StateOk ctx0 Γ .ivar0 m) (hk : m.kont = [])
    (hcls : cls ∈ primitiveErrorClasses) (msg : String) :
    StepSpec m Γ τ (.next (Interp.raiseErr m cls msg)) := by
  have hp := List.all_eq_true.mp hm.primitiveErrors cls hcls
  simp only [primitiveErrorB, Bool.and_eq_true, Bool.not_eq_true'] at hp
  let obj : Object := { klass := cls, payload := .exc msg }
  let n : Machine := { m with heap := pushHeap m.heap obj }
  have he : Ext m n := ext_push obj hm.sat hm.core.basicSelf
    (fun c => by simp [obj]) rfl rfl hp.1.1.1
  have hc : classOf n.heap (.ref m.heap.objs.size) = cls := by
    simp [n, classOf, pushHeap_get_self, obj]
  have hsafe : EscOk n (.raiseJ (.ref m.heap.objs.size)) := by
    simp only [EscOk, Semantics.isTypeError, Semantics.typeErrorFamily, List.any_cons,
      List.any_nil, isA, hc, he.ancestors, hp.1.1.2, hp.1.2, hp.2, Bool.false_or]
  have h := RunSpec.answer (a := .esc (.raiseJ (.ref m.heap.objs.size)))
    (show ResultOk m Γ τ _ n from ⟨Framed.of_ext he, hsafe, fun _ hv => by cases hv⟩)
  simpa only [StepSpec, Interp.raiseErr, Builtins.allocExc, Heap.alloc, n, pushHeap, obj,
    deliverA, Answer.ctl, hk] using h

theorem stepSpec_zeroDiv {Γ : Env} {m : Machine} {τ : Ty}
    (hm : StateOk ctx0 Γ .ivar0 m) (hk : m.kont = []) (msg : String) :
    StepSpec m Γ τ (.next (Interp.raiseErr m Boot.zeroDivisionErrorId msg)) :=
  stepSpec_error hm hk (by simp [primitiveErrorClasses]) msg

theorem string_add_run (m : Machine) (a b : Value) :
    Builtins.run "String#+" a [b] m = Builtins.runStrings "String#+" a [b] m := by
  simp only [Builtins.run,
    show Builtins.byteStrAwareBids.contains "String#+" = true from rfl,
    Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

#print axioms stepSpec_string
#print axioms stepSpec_zeroDiv
end Ratchet.Denote.Typed
