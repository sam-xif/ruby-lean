import Denote.Typed.PrimitiveAlloc

/-! Bare `x` follows ordinary dispatch to a non-type-error NameError. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem invoke_x (m : Machine) (recv : Value) :
    Interp.invoke m recv .vcall "x" [] none [] =
      Interp.invoke.invokeDispatch m recv .vcall "x" [] none [] := by
  rw [Interp.invoke.eq_def]
  simp only [show ("x" == "send" || "x" == "public_send" || "x" == "__send__") = false from rfl,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases recv with
  | ref o =>
    cases hp : (m.heap.get o).payload <;> simp only [hp]
    all_goals first | rfl | simp [Interp.invoke.invokeMaybeNew]
  | _ => rfl

theorem dispatchMiss_x {Γ : Env} {m : Machine} (hm : StateOk ctx0 Γ .ivar0 m)
    (hk : m.kont = []) :
    StepSpec m Γ .any (Interp.dispatchMiss m m.currentFrame.self .vcall "x" [] none) := by
  simp only [Interp.dispatchMiss, Interp.tryIterator, Interp.tryMixin, Interp.tryReflect]
  cases Interp.crubySingletonShadow m.heap m.currentFrame.self "x" with
  | some _ => trivial
  | none =>
    cases Interp.crubyShadow m.heap (ancestors m.heap (classOf m.heap m.currentFrame.self)) "x" with
    | some _ => trivial
    | none =>
      cases Interp.mixinShadow m m.currentFrame.self "x" with
      | some _ => trivial
      | none =>
        cases hl : Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) "method_missing" with
        | none => exact stepSpec_error hm hk (by simp [primitiveErrorClasses]) _
        | some p =>
          obtain ⟨owner, md⟩ := p
          have hb := hm.missFree rfl rfl owner md hl
          cases he : md.builtin with
          | none => rw [he] at hb; cases hb
          | some bid =>
            simp only [he, Option.isNone, Bool.false_eq_true, ↓reduceIte]
            exact stepSpec_error hm hk (by simp [primitiveErrorClasses]) _

theorem SemA.bareName {Γ : Env} : SemSafeA Γ (.vcall "x") .any Γ := by
  apply semSafe_of_runSpec
  intro m hm
  apply RunSpec.rebase (middle := evalFrom m (.vcall "x")) ?_ (Framed_reCtl m _ [])
  apply RunSpec.of_stepSpec (by rfl)
  change StepSpec (evalFrom m (.vcall "x")) Γ .any
    (Interp.invoke (evalFrom m (.vcall "x")) m.currentFrame.self .vcall "x" [] none [])
  rw [invoke_x, Interp.invoke.invokeDispatch]
  have hm' := StateOk_reCtl hm (.eval (.vcall "x")) []
  have hx : lookup (evalFrom m (.vcall "x")).heap m.currentFrame.self "x" = none :=
    hm.bareFree "x" .x rfl rfl
  rw [hx]
  have h := dispatchMiss_x hm' rfl
  exact h

#print axioms SemA.bareName

-- Both sites really raise; only the bare-name site's exception is outside type-stuck.
#guard match Interp.run 100 (evalFrom bootMachine (.vcall "x")) with
  | .uncaught exc m => classOf m.heap exc == Boot.nameErrorId && !Semantics.isTypeError m.heap exc
  | _ => false
#guard Semantics.typeStuck (Interp.run 100 (evalFrom bootMachine (.send none "x" [] none)))

end Ratchet.Denote.Typed
