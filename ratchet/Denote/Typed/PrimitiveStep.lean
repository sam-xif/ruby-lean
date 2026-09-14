import Denote.Typed.PrimitiveFacts

/-! A dispatch step may return a value, raise a non-type exception, or gate. All three
are represented here without discarding the answer contract. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def StepSpec (origin : Machine) (Γ : Env) (τ : Ty) : StepResult → Prop
  | .next n => RunSpec origin n Γ τ
  | .unsupported _ => True
  | _ => False

theorem RunSpec.of_stepSpec {origin start : Machine} {Γ : Env} {τ : Ty}
    (ha : answerPoint start = none) (h : StepSpec origin Γ τ (Interp.stepFn start)) :
    RunSpec origin start Γ τ := by
  cases hs : Interp.stepFn start with
  | next n => exact RunSpec.step ha hs (by simpa [hs, StepSpec] using h)
  | unsupported r => exact RunSpec.unsupported ha hs
  | done v n => simp [hs, StepSpec] at h
  | uncaught v n => simp [hs, StepSpec] at h
  | stuck msg => simp [hs, StepSpec] at h

theorem stepSpec_value {Γ : Env} {τ : Ty} {m : Machine} {v : Value}
    (hm : StateOk ctx0 Γ .ivar0 m) (hk : m.kont = []) (hd : denM τ m v) :
    StepSpec m Γ τ (.next (Interp.withCtl m (.value v))) := by
  have h := RunSpec.answer (a := .val v)
    (show ResultOk m Γ τ (.val v) m from ⟨.refl m, hd, fun _ hv => by cases hv; exact hm⟩)
  simpa only [StepSpec, Interp.withCtl, deliverA, Answer.ctl, hk] using h

def builtinStep (r : BRes) : StepResult :=
  match r with
  | .ok v n => .next (Interp.withCtl n (.value v))
  | .err cls msg n => .next (Interp.raiseErr n cls msg)
  | .throwV v n => .next (Interp.withCtl n (.jump (.raiseJ v)))
  | .unsupported r => .unsupported r

theorem invoke_plain {site : SendSite} {m : Machine} {recv : Value} {name : String} {args : List Value}
    (hn : (name == "send" || name == "public_send" || name == "__send__") = false)
    (hr : ∀ o, recv = .ref o → ∃ s, (m.heap.get o).payload = .str s) :
    Interp.invoke m recv site name args none [] =
      Interp.invoke.invokeDispatch m recv site name args none [] := by
  rw [Interp.invoke.eq_def]
  simp only [hn, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases recv with
  | ref o => obtain ⟨s, hs⟩ := hr o rfl; simp only [hs]
  | _ => rfl

theorem primitive_invoke {site : SendSite} {Γ : Env} {m : Machine} {recv : Value} {name bid : String}
    {args : List Value} {k : ObjId} (hm : StateOk ctx0 Γ .ivar0 m)
    (hrow : (k, name, bid) ∈ primitiveMethods) (hc : classOf m.heap recv = k)
    (hn : (name == "send" || name == "public_send" || name == "__send__") = false)
    (hr : ∀ o, recv = .ref o → ∃ s, (m.heap.get o).payload = .str s)
    (hd : Builtins.deferTwin? m.heap bid recv args = none)
    (hraise : (bid == "Object#raise") = false) :
    Interp.invoke m recv site name args none [] = builtinStep (Builtins.run bid recv args m) := by
  obtain ⟨owner, md, hl, hb, hu, hv, hp, hs⟩ := primitive_lookup hm hrow
  rw [invoke_plain hn hr]
  apply invokeDispatch_builtin (owner := owner) (md := md) _ hb hu hv hp _ hd hraise
  · rw [lookup_eq_methodOn, hc]; exact hl
  · simpa only [hc] using hs

theorem invoke_int_add {site : SendSite} {Γ : Env} {m : Machine} (hm : StateOk ctx0 Γ .ivar0 m) (x y : Int) :
    Interp.invoke m (.int x) site "+" [.int y] none [] =
      .next (Interp.withCtl m (.value (.int (x + y)))) := by
  rw [primitive_invoke (bid := "Integer#+") (k := Boot.integerId) hm
    (by simp [primitiveMethods]) rfl (by rfl)
    (by intro o ho; cases ho) (by rfl) (by rfl), int_add_run]
  rfl

#print axioms invoke_int_add
end Ratchet.Denote.Typed
