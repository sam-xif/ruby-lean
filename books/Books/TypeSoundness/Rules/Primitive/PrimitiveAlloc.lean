import Books.TypeSoundness.Rules.Primitive.ExceptionAlloc

/-! Primitive allocation results: a String value or a checked non-type-error exception. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem stepSpec_string {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} (hm : StateOk κ Γ I m)
    (hk : m.kont = []) (s : String) (binary : Bool) :
    StepSpec m Γ (.cls "String") (builtinStep (Builtins.okStrEnc m binary s)) κ I := by
  have he := ext_push (m := m) (strObj s binary) hm.sat hm.core.basicSelf
    (fun c => by simp [strObj]) rfl rfl (by simpa [strObj] using hm.core.stringBasic)
  obtain ⟨hn, hd⟩ := strLit_alloc_ok (Γ := Γ) (m := m) (s := s) [] hm binary
  have hf := (Framed.of_ext he).trans (Framed_reCtl _ (.value (.ref m.heap.objs.size)) [])
  have h := RunSpec.answer (a := .val (.ref m.heap.objs.size))
    (show ResultOk m Γ (.cls "String") _ _ κ I from
      ⟨hf, hd, fun _ hv => by cases hv; exact hn⟩)
  simpa only [StepSpec, builtinStep, Builtins.okStrEnc, Builtins.allocStrEnc,
    Heap.alloc, pushHeap, strObj, Interp.withCtl, deliverA, Answer.ctl, reCtl, hk] using h

theorem stepSpec_nameError {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {τ : Ty}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (msg : String) :
    StepSpec m Γ τ (.next (Interp.raiseErr m Boot.nameErrorId msg)) κ I := by
  have h := errorObject_answer (τ := τ) hm (cls := Boot.nameErrorId)
    (by simp [primitiveErrorClasses]) msg (.ref m.heap.objs.size) 0
  simpa [StepSpec, Interp.raiseErr, Builtins.allocExc, Builtins.allocStr,
    Builtins.allocStrEnc, Heap.alloc, errorObjectMachine, errorMessageMachine, pushHeap,
    strObj, deliverA, Answer.ctl, hk, Boot.nameErrorId] using h

theorem stepSpec_keyError {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {τ : Ty}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (msg : String) :
    StepSpec m Γ τ (.next (Interp.raiseErr m Boot.keyErrorId msg)) κ I := by
  have h := errorObject_answer (τ := τ) hm (cls := Boot.keyErrorId)
    (by simp [primitiveErrorClasses]) msg (.ref m.heap.objs.size) 0
  simpa [StepSpec, Interp.raiseErr, Builtins.allocExc, Builtins.allocStr,
    Builtins.allocStrEnc, Heap.alloc, errorObjectMachine, errorMessageMachine, pushHeap,
    strObj, deliverA, Answer.ctl, hk, Boot.keyErrorId] using h

theorem stepSpec_zeroDiv {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {τ : Ty}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (msg : String) :
    StepSpec m Γ τ (.next (Interp.raiseErr m Boot.zeroDivisionErrorId msg)) κ I :=
  runSpec_zeroDivisionError hm hk msg

theorem string_add_run (m : Machine) (a b : Value) :
    Builtins.run "String#+" a [b] m = Builtins.runStrings "String#+" a [b] m := by
  simp only [Builtins.run,
    show Builtins.byteStrAwareBids.contains "String#+" = true from rfl,
    Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [show ("String#+".endsWith "#==" || "String#+".endsWith "#eql?" ||
    "String#+".endsWith "#!=" || Builtins.pureEqualityBids.contains "String#+") = false from by decide +kernel,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

#print axioms stepSpec_nameError
#print axioms stepSpec_string
#print axioms stepSpec_zeroDiv
end Checker.Soundness.Typed
